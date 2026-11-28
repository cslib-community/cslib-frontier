/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Crypto.Computational.PseudorandomGenerator.NextBit

/-!
# Yao's next-bit characterization for uniform pseudorandom generators
-/

register_result "yao-next-bit" where
  title := "Yao’s next-bit theorem for polynomial-time length-regular stretching generators"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorems 3.4 and 3.6",
      locator := "Version 0.6, Section 3.5, printed pp. 64 and 67. Attack Game 3.2 and \
        Definition 3.3, p. 64." }
  ]
  theorems := [
    Cslib.Crypto.pseudorandomGenerator_iff_nextBitUnpredictable,
    Cslib.Crypto.pseudorandomGenerator_iff_nextBitUnpredictableRandomIndex
  ]
  scope := "A deterministic polynomial-time generator maps each n-bit seed to L(n) bits, \
    with L(n) > n. Seeds are uniform and adversaries are uniform strict PPT with unary security \
    parameter. In Attack Game 3.2 the predictor chooses a binary position before seeing the \
    prefix and retains encodable state. An invalid position yields a fair coin. The reduction \
    from prediction to distinguishing preserves advantage. In the reverse direction the \
    strict-clock reduction divides distinguishing advantage by D = dyadicSize (L(n) - 1), \
    with D ≤ 2L(n). In the single-stage variant the challenger draws the position uniformly \
    from the whole output. The predictor built from a distinguisher then divides its advantage \
    by exactly L(n), and the distinguisher built from a predictor retains L(n)/D of its advantage."
