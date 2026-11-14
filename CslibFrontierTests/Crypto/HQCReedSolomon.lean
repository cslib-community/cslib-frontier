/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Primitives.HQC.ReedSolomon

/-!
# Tests: the shortened Reed–Solomon layer used by HQC

The source locator contains exactly `t1 + 1` coefficients.  In particular, the Chien root test
for the concrete Berlekamp result is evaluation of that bounded polynomial; no coefficient above
`t1` can affect it while remaining invisible to `Z` or the odd-locator denominator.
-/

namespace CslibFrontierTests.Crypto.HQCReedSolomon

open Polynomial Cslib.Crypto.HQC

example :
    let p := hqcReedSolomonParameters .hqc1
    (p.length, p.messageLength, p.capacity) = (46, 16, 15) := by
  decide

example :
    let p := hqcReedSolomonParameters .hqc3
    (p.length, p.messageLength, p.capacity) = (56, 24, 16) := by
  decide

example :
    let p := hqcReedSolomonParameters .hqc5
    (p.length, p.messageLength, p.capacity) = (90, 32, 29) := by
  decide

/-- Regression for the capped-locator boundary: even the first coefficient beyond the source
array is identically zero. -/
example {F : Type*} [Semiring F] (p : HQCReedSolomonParameters)
    (locator : HQCRSErrorLocator p F) :
    (hqcRSLocatorPolynomial p locator).coeff (p.capacity + 1) = 0 :=
  hqcRSLocatorPolynomial_coeff_eq_zero p locator (by omega)

/-- The concrete Berlekamp stage feeds Chien evaluation only through the source's `t1 + 1`
coefficients. -/
example {F : Type*} [Field F] [CharP F 2] [DecidableEq F]
    (p : HQCReedSolomonParameters) (syndromes : Fin (2 * p.capacity) → F) (beta : F) :
    (hqcRSLocatorPolynomial p (hqcRSBerlekampLocator p syndromes)).eval beta =
      ∑ i, hqcRSBerlekampLocator p syndromes i * beta ^ (i : ℕ) :=
  hqcRSLocatorPolynomial_eval p (hqcRSBerlekampLocator p syndromes) beta

end CslibFrontierTests.Crypto.HQCReedSolomon
