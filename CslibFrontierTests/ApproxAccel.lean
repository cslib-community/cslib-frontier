/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.ApproxMain
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Approximate

/-! Tests of the Laurent-polynomial bookkeeping of approximate accelerators (Appendix N of
[AnthropicVPVNP2026]) under ordinary imports:

* constants have order `0`, and orders add under products;
* every Laurent polynomial has a span, and spans multiply;
* the logarithm bound used to choose the scales. -/

namespace CslibFrontierTests.ApproxAccel

open Cslib.Circuits.Arithmetic.Separation.Interpreter LaurentPolynomial

/-- Constants have no terms below `ε ^ 0`, and products of such have none either. -/
example (a b : ℤ) :
    OrderGE 0 (algebraMap ℤ ℤ[T;T⁻¹] a * algebraMap ℤ ℤ[T;T⁻¹] b) := by
  simpa using (OrderGE.of_algebraMap (E := ℤ) a).mul (OrderGE.of_algebraMap (E := ℤ) b)

/-- Every Laurent polynomial has exponents within some span. -/
example (P : ℤ[T;T⁻¹]) : ∃ n, Span n P := exists_span P

/-- Spans add under products: `Span 0 1` and `Span n P` give `Span n P`. -/
example (n : ℕ) (P : ℤ[T;T⁻¹]) (h : Span n P) : Span (0 + n) (1 * P) := (Span.one 0).mul h

/-- `4 lg u ≤ lg (u ^ 5)` for `u ≥ 8`. -/
example : 4 * lg 8 ≤ lg (8 ^ 5) := le_lg_four le_rfl

end CslibFrontierTests.ApproxAccel
