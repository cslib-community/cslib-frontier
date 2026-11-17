/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.Scheme
public import CslibFrontier.Crypto.Game.Experiment

/-!
# One-way public-key encryption

Attack Game 12.6 of Boneh and Shoup ([BonehShoup2023], Section 12.6, printed p. 495): "The
challenger computes `(pk, sk) ←R G_a(), x ←R 𝒳, r ←R ℛ, y ← E_a(pk, x; r)`, and sends `(pk, y)`
to the adversary. The adversary outputs `x̂`". It wins "if `x̂ = x`", and its advantage
`OWadv[𝒜, ℰ_a]` is "the probability that `𝒜` wins the game".

`PKE.owExperiment E sampleMsg A` is this game for a scheme `E : PKE PK SK M C`, with the message
drawn from `sampleMsg`; `PKE.owAdvantage` is the adversary's success probability. The book draws
`x` uniformly from the message space; a sampler lets a client choose the message law, for example
the uniform law on a cyclic group through a generator. The book's `x̂ ∈ ℛ` is read as `x̂ ∈ 𝒳`.
Definition 12.5 (one way: negligible advantage for every efficient adversary) is not stated here
as a predicate; `CDH.elGamal_oneWay` states it for multiplicative ElGamal and typed adversaries.

## Main definitions

* `Cslib.Crypto.PKE.owExperiment`: Attack Game 12.6.
* `Cslib.Crypto.PKE.owAdvantage`: the adversary's advantage `OWadv`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 12.6, Attack Game 12.6 (printed p. 495).
-/

public section

namespace Cslib.Crypto.PKE

open Probability
open scoped NNReal

variable {PK SK M C : Type} [DecidableEq M]

/-- **Attack Game 12.6** (one-way encryption, [BonehShoup2023], Section 12.6, p. 495): draw a key
pair, a message `x ← sampleMsg` and a ciphertext `y ← E.encrypt pk x`, give `(pk, y)` to the
adversary, and accept when it outputs `x`. -/
@[expose]
def owExperiment (E : PKE PK SK M C) (sampleMsg : ProbComp M) (A : PK → C → ProbComp M) :
    Experiment := do
  let keys ← E.keyGen
  let x ← sampleMsg
  let y ← E.encrypt keys.1 x
  let x' ← A keys.1 y
  return decide (x' = x)

/-- The advantage `OWadv[A, E]` of Attack Game 12.6: the probability that `A` recovers the
message. -/
@[expose]
noncomputable def owAdvantage (E : PKE PK SK M C) (sampleMsg : ProbComp M)
    (A : PK → C → ProbComp M) : ℝ≥0 :=
  Experiment.succProbability (owExperiment E sampleMsg A)

end Cslib.Crypto.PKE
