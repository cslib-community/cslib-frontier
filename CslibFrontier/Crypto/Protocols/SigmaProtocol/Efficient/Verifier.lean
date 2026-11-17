/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Efficient

/-!
# Efficient verifiers for Sigma protocols

Uniform polynomial-time verification certificates for indexed families of Sigma protocols: one
deterministic polynomial-time word function computes `(P i).verify` from the encoded index,
statement, commitment, challenge and response.

## Main definitions

* `Cslib.Crypto.Protocols.SigmaProtocol.VerifierRealizedBy`: a word function computes `(P i).verify`
  on encodings.
* `Cslib.Crypto.Protocols.SigmaProtocol.EfficientVerifier`: uniform deterministic polynomial-time
  verification for an indexed family of Sigma protocols.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Turing.MultiTapeTM

variable {I : Type} {X Y T C Z : I → Type}

/-- The word function `f` computes the verifier of the protocol family `P` on encodings: from the
index and the encoded statement, commitment, challenge and response, it returns `(P i).verify`. -/
def VerifierRealizedBy (P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i))
    (enc : Encoding I Y T C Z)
    (f : I × List Bool × List Bool × List Bool × List Bool → Bool) : Prop :=
  ∀ i y t c z,
    f (i, enc.statement i y, enc.commitment i t, enc.challenge i c, enc.response i z) =
      (P i).verify y t c z

/-- **Efficient verification** for an indexed family of Sigma protocols: one deterministic
polynomial-time function of the index and words computes `(P i).verify` on encodings. -/
def EfficientVerifier (P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i))
    (enc : Encoding I Y T C Z) : Prop :=
  ∃ f, ComputableInPolyTime f
      (encPair enc.index (encPair encBits (encPair encBits (encPair encBits encBits)))) encBool ∧
    VerifierRealizedBy P enc f

end Cslib.Crypto.Protocols.SigmaProtocol
