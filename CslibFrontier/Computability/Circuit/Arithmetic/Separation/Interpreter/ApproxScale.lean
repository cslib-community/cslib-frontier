/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Scale
public import CslibFrontier.Foundations.Data.List.Forall2
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.ApproxRound
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Polynomial.Laurent

/-!
# From one scale to the next, approximately

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Appendix N (Proposition N.4, Theorem N.5) of the paper; module `NS1.ApproxScale`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Interpreter

open Cslib.Circuits.Arithmetic.Separation.Interpreter.Tree LaurentPolynomial

variable {A : Type} [CommRing A] {θ : List Bool → A} {E : Type} [CommRing E] [Algebra A E]

theorem size_roundA {R : Type} (K K' : KT R) (B B' J : ℕ) (D G p : Tree) :
    (roundA K B K' B' J D G p).code.size ≤ 2 * D.size + G.size + p.size +
        (gt id J B K [false]).code.size +
      (gt id J B' K' [true]).code.size + 2 * WF.code.size + UF.code.size + 2000 := by
  have := size_LP D
  simp only [roundA, stepA, rebF, app, ZE, Fm.code, Tree.size, size_num]
  omega

/-- **The exponents of the outer weights**: products of powers of constants of span `M`. -/
theorem span_expand_budg {K : KT E[T;T⁻¹]} {M B J : ℕ} (hM : K.All (Span M)) {q : Bt × E[T;T⁻¹]}
    (hq : q ∈ (K.expand B).budg J) : Span ((K.expand B).nds * 2 ^ J * (2 ^ B * M)) q.2 :=
  span_budg (hM.expand (Q := Span (2 ^ B * M)) fun _ hc _ hb =>
    (hc.pow _).mono (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hb.le))) hq

end Cslib.Circuits.Arithmetic.Separation.Interpreter
