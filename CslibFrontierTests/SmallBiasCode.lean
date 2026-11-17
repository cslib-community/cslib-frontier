/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Probability.SmallBias.Code

/-! [Goldreich2007DraftR4], Exercise 8.41, in the printed form: a generator `G : {0,1}^k → {0,1}^ℓ`
is an `ε`-bias generator exactly when its linear code from `ℓ`-bit messages to words indexed by the
`2^k` seeds maps every two distinct messages to codewords at distance between `(1 - ε) 2^(k-1)` and
`(1 + ε) 2^(k-1)`; the `j`-th bit of the codeword of the `i`-th unit vector is the `i`-th bit of
`G j`; and every binary linear code of these lengths arises from a generator. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SmallBiasCode

open Cslib.BitString Cslib.Probability

variable {k ℓ : ℕ}

-- The correspondence of Exercise 8.41 for seeds `{0,1}^k`, with `2^(k-1)` written `2^k / 2`.
example (G : (Fin k → Bool) → Fin ℓ → Bool) (ε : ℝ) :
    IsSmallBias ε ((PMF.uniformOfFintype (Fin k → Bool)).map G) ↔
      ∀ u v : Fin ℓ → Bool, u ≠ v →
        (1 - ε) * 2 ^ k / 2 ≤ hammingDist (sampleCode G u) (sampleCode G v) ∧
          (hammingDist (sampleCode G u) (sampleCode G v) : ℝ) ≤ (1 + ε) * 2 ^ k / 2 := by
  rw [isSmallBias_map_iff_hammingDist_sampleCode]
  simp

-- The guideline's description of the code through the unit vectors.
example (G : (Fin k → Bool) → Fin ℓ → Bool) (i : Fin ℓ) (j : Fin k → Bool) :
    sampleCode G (Pi.single i true) j = G j i :=
  sampleCode_single G i j

-- Every binary linear code from `ℓ` bits to `2^k` bits is the code of a generator.
example (C : (Fin ℓ → Bool) →ₗ[Bool] (Fin k → Bool) → Bool) :
    ∃ G : (Fin k → Bool) → Fin ℓ → Bool, sampleCode G = C :=
  ⟨_, sampleCode_ofCode C⟩

-- The identity generator on one bit is `0`-biased, so its code (the repetition of the message
-- bit on the seeds where it is read) has its two codewords at distance exactly `1 = 2^1 / 2`.
example : hammingDist (sampleCode (fun s : Fin 1 → Bool => s) 0)
    (sampleCode (fun s : Fin 1 → Bool => s) (Pi.single 0 true)) = 1 := by
  decide

end CslibFrontierTests.SmallBiasCode
