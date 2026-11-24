/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.Tribes

/-!
# Collected results: the Fourier coefficients of Tribes
-/

register_result "odonnell-tribes-fourier-coefficients" where
  title := "The Fourier coefficients of Tribes"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Proposition 4.14",
      locator := "arXiv:2105.10386v1, §4.2, printed p. 97" }
  ]
  theorems := [Cslib.BitString.fourierCoeff_signVal_tribes_empty,
    Cslib.BitString.fourierCoeff_signVal_tribes_of_ne_empty]
  scope := "For all w s : ℕ, Tribes_{w,s} is tribes w s on s * w bits, bit i of tribe j being \
    coordinate finProdFinEquiv (j, i), read as signs through signVal (true ↦ -1, the book's \
    True). A set T of coordinates is split into its parts tribePart T j : Finset (Fin w), the \
    book's T_j. With k = #{j | tribePart T j ≠ ∅} the number of tribes T meets, the \
    coefficient on ∅ is 2 (1 - 2^(-w))^s - 1, and on T ≠ ∅ (equivalently k > 0) it is \
    2 (-1)^(k + #T) 2^(-k w) (1 - 2^(-w))^(s - k). These are the book's two cases, with no \
    restriction on w or s."
