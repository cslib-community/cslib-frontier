/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.PKE.ExplicitCoin
import CslibFrontier.Probability.PMF.ToReal

/-!
# Event bounds for explicit-coin PKE correctness

This file contains the scheme-independent measure plumbing for proving
`ExplicitCoinPKE.DeltaCorrect`. A scheme supplies a coin event containing every honest
decryption failure, a pointwise event-probability bound for generated keys, and a finite bound on
the key-generation expectation. The lemmas here lift those facts through the maximum over messages
and the expectation over generated keys.

The event and its bound remain scheme-specific. In particular, this module makes no independence,
distribution, or decoder assumption.

## Main definitions

This module adds no new definitions. It works with `ExplicitCoinPKE.msgFailProb`,
`ExplicitCoinPKE.keyPairMaxFailProb`, and `ExplicitCoinPKE.DeltaCorrect`.

## Main results

* `Cslib.Crypto.Protocols.ExplicitCoinPKE.msgFailProb_le_event`: event inclusion bounds one
  message's decryption-failure probability.
* `Cslib.Crypto.Protocols.ExplicitCoinPKE.keyPairMaxFailProb_le_of_msgFailProb_le`: a common
  message bound controls the worst-message probability.
* `Cslib.Crypto.Protocols.ExplicitCoinPKE.deltaCorrect_of_keyGen_expect_le`: an extended-
  nonnegative key-expectation bound implies `DeltaCorrect`.

## References

* [Hofheinz, Hövelmanns and Kiltz, *A Modular Analysis of the Fujisaki--Okamoto
  Transformation*][HofheinzHoevelmannsKiltz2017], §2.1.
-/

public section

namespace Cslib.Crypto.Protocols

open Probability

namespace ExplicitCoinPKE

variable {PK SK M R CT : Type}

/-- If every honest decryption failure for a fixed key pair and message belongs to `event`, then
the message failure probability is at most the probability of `event`. -/
theorem msgFailProb_le_event (P : ExplicitCoinPKE PK SK M R CT)
    (pk : PK) (sk : SK) (m : M) (event : Set R)
    (hfail : ∀ r, P.dec sk (P.encDet pk m r) ≠ some m → r ∈ event) :
    P.msgFailProb pk sk m ≤
      ((ProbComp.eval P.sampleCoins).toOuterMeasure event).toReal := by
  rw [msgFailProb]
  apply PMF.toOuterMeasure_toReal_mono
  intro r hr
  exact hfail r hr

/-- A real bound that holds for every message also bounds the fixed key pair's maximum
decryption-failure probability. -/
theorem keyPairMaxFailProb_le_of_msgFailProb_le [Fintype M] [Nonempty M]
    (P : ExplicitCoinPKE PK SK M R CT) (pk : PK) (sk : SK) (bound : ℝ)
    (hbound : ∀ m, P.msgFailProb pk sk m ≤ bound) :
    P.keyPairMaxFailProb pk sk ≤ bound := by
  rw [keyPairMaxFailProb, Finset.sup'_le_iff]
  intro m _
  exact hbound m

/-- An extended-nonnegative upper bound on the expectation over generated keys of the
worst-message failure probability gives `DeltaCorrect` at its real coercion. Finiteness is
explicit because an arbitrary key distribution and score can have infinite expectation. -/
theorem deltaCorrect_of_keyGen_expect_le [Fintype M] [Nonempty M]
    {P : ExplicitCoinPKE PK SK M R CT} {bound : ENNReal}
    (hle : P.keyGen.expect (fun keys => ENNReal.ofReal
      (P.keyPairMaxFailProb keys.1 keys.2)) ≤ bound)
    (hfinite : bound ≠ ⊤) : P.DeltaCorrect bound.toReal := by
  unfold DeltaCorrect
  exact ENNReal.toReal_mono hfinite hle

end ExplicitCoinPKE

end Cslib.Crypto.Protocols
