/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.AlgebraicValueBounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder

/-! # Binary computation of dyadic root-label precision bounds -/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- The uniform derivative norm allowance is computable from binary bounds. -/
theorem iterateDerivativeNormExponent_polyTime {α : Type} {enc : α ↪ List Bool}
    {D b : α → ℕ} (hD : ComputableInPolyTime D enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => Polynomial.iterateDerivativeNormExponent (D w) (b w))
      enc encNat :=
  binary_add' hb (binary_mul' (unary_to_binary.comp (binary_size.comp hD)) hD)

/-- The common root-label precision is computable in polynomial time from binary bounds. -/
@[fun_prop] theorem derivativeRootLabelPrecision_polyTime {α : Type} {enc : α ↪ List Bool}
    {D b : α → ℕ} (hD : ComputableInPolyTime D enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => Polynomial.derivativeRootLabelPrecision (D w) (b w))
      enc encNat := by
  have hdegree := binary_add' hD hD
  have hdegreeSize := unary_to_binary.comp (binary_size.comp hdegree)
  have hnorm := iterateDerivativeNormExponent_polyTime hD hb
  have hlower := binary_add'
    (binary_mul' (binary_add' hdegreeSize (binary_max' hb (binary_add' hnorm (.const 1))))
      hdegree) (.const 1)
  have hupper := binary_add' hnorm (binary_mul' hD (binary_add' hb (.const 1)))
  simpa only [Polynomial.derivativeRootLabelPrecision, Polynomial.algebraicValuePrecision,
    Function.comp_apply] using binary_max' hlower hupper

end Cslib.Complexity.RealAlgebraic
