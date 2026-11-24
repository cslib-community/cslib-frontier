/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.AccSize
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.LowDegProg
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.NoAcc
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Transfer
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Rat.Init
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Tests of the low-degree layer:

* the gate list of a circuit (`ComputedWithin.exists_steps`);
* polynomials along a line;
* full tries of constants;
* the headline results `lem_lowdeg` (Lemma K.2) and `thm_noacc` (Theorem K.6);
* the transfer of circuits to an algebraically closed field. -/

namespace CslibFrontierTests.LowDegree

open MvPolynomial Cslib.Circuits.Arithmetic Cslib.Circuits.Arithmetic.Separation.Interpreter

/-- A variable is computed with one node, so the gate list has it at entry `0`. -/
example : ∃ l : ℕ → MvPolynomial (Fin 1) ℚ, l 0 = X 0 := by
  obtain ⟨l, -, k, hk, e⟩ := (computedWithin_X (K := ℚ) (0 : Fin 1)).exists_steps
  obtain rfl : k = 0 := by omega
  exact ⟨l, e⟩

/-- Every entry of the gate list of `X 0 * X 0` is a variable, a constant, or the sum or product of
two earlier entries. -/
example : ∃ l : ℕ → MvPolynomial (Fin 1) ℚ, (∀ k < 3, (∃ i, l k = X i) ∨ (∃ a, l k = C a) ∨
    (∃ i < k, ∃ j < k, l k = l i + l j) ∨ (∃ i < k, ∃ j < k, l k = l i * l j)) ∧
    ∃ k < 3, l k = X 0 * X 0 :=
  ((computedWithin_X (K := ℚ) (0 : Fin 1)).mul (computedWithin_X 0)).exists_steps

/-- Along a line, the value at `u` of a polynomial of degree at most `1` is the sum of its first two
coefficients. -/
example (u : Fin 1 → ℚ) : ∑ i ∈ Finset.range 2, (line u (X 0 : MvPolynomial (Fin 1) ℚ)).coeff i =
    u 0 := by
  rw [sum_coeff_line_eq_eval (d := 1) _ _ (by simp) (by norm_num)]
  simp

/-- The full trie of depth `1` has the constant `f [true]` at the name `true, false`. -/
example (f : List Bool → ℚ) : (KT.full 1 f).lk ([true] ++ [false]) = f [true] :=
  KT.lk_full f rfl

/-- Along a line, the coefficient of degree `2` of `X 0 * X 0` is its homogeneous part of degree
`2` at the point. -/
example (u : Fin 1 → ℚ) : (line u (X 0 * X 0 : MvPolynomial (Fin 1) ℚ)).coeff 2 =
    eval u (homogeneousComponent 2 (X 0 * X 0)) :=
  coeff_line u _ 2

/-- **Lemma K.2** for the variable `X (0, some false)` over `ℚ`, computed within one node, with one
place and degree `1`: the trie of constants of its program has height at most `4`. -/
example : ∃ K : KT ℚ, K.ht ≤ 3 * 0 + 0 + 4 := by
  obtain ⟨c, hc⟩ := lem_lowdeg
  obtain ⟨K, -, -, hht, -⟩ := hc ℚ 0 0 1 1 1 (X ((0 : Fin 1), some false)) (computedWithin_X _)
    (by norm_num) (by norm_num)
  exact ⟨K, hht⟩

/-- **Theorem K.6** for `A = ℤ` and the field `ZMod 2`, with `h = 17`: given Theorem C, small
accelerators do not exist at large scales. -/
example (θ : List Bool → ℤ) {C₀ v₀ : ℕ} (hcut : CutHyp θ (16 * 17) C₀ v₀) :
    ∃ C v₁ : ℕ, ∀ v, v₁ ≤ v → ∀ a, lg v ^ (C * a) ≤ v →
      ¬ HasAcc θ (ZMod 2) (16 * 17) v (v ^ a) := by
  have : Fact (1 < 2) := ⟨by norm_num⟩
  obtain ⟨C, v₁, h⟩ := thm_noacc le_rfl hcut
  exact ⟨C, v₁, fun v hv a ha => h v hv a ha (ZMod 2)⟩

/-- A circuit over `ZMod 2` for a polynomial with integer coefficients gives one of the same size
over the algebraic closure of `ZMod 2`. -/
example (q : MvPolynomial (Fin 2) ℤ) {S : ℕ}
    (h : ComputedWithin (map (Int.castRingHom (ZMod 2)) q) S) :
    ComputedWithin (map (Int.castRingHom (AlgebraicClosure (ZMod 2))) q) S :=
  Cslib.Circuits.Arithmetic.Separation.lem_transfer 2 q h

/-- A polynomial computed within `s` nodes lifts along a ring map whose range holds its
constants: along the surjective cast `ℤ → ZMod 2`, the variable `X 0` lifts. -/
example : ∃ Q : MvPolynomial (Fin 1) ℤ, ComputedWithin Q 1 ∧
    map (Int.castRingHom (ZMod 2)) Q = X 0 := by
  obtain ⟨S, hS⟩ := (computedWithin_X (K := ZMod 2) (0 : Fin 1)).exists_finset_lift
  exact hS (Int.castRingHom (ZMod 2)) fun t _ => ZMod.intCast_surjective t

/-- An approximation of `X 0` within one node over `ZMod 2` gives a circuit of one node over the
algebraic closure with constants in `KK[ε, ε⁻¹]`, whose constant term is `X 0` and which has no
negative powers of `ε`. -/
example : ∃ P : MvPolynomial (Fin 1) (LaurentPolynomial (AlgebraicClosure (ZMod 2))),
    ComputedWithin P 1 ∧ ∀ d : Fin 1 →₀ ℕ, (∀ i : ℤ, i < 0 → (P.coeff d).coeff i = 0) ∧
      (P.coeff d).coeff 0 =
        (map (Int.castRingHom (AlgebraicClosure (ZMod 2)))
          (X 0 : MvPolynomial (Fin 1) ℤ)).coeff d :=
  Cslib.Circuits.Arithmetic.Separation.lem_transfer_approx (F := ZMod 2) 2 (X 0) (by
    rw [map_X]
    exact (computedWithin_X 0).approximatedWithin)

end CslibFrontierTests.LowDegree
