/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import CslibFrontier.Crypto.Computational.WordAggregateSignature
import CslibFrontier.Tactic.PPT

/-!
# Appending a hash of the keys and messages to an aggregate signature

Exercise 15.11(c) of [BonehShoup2023] (p. 675) makes an aggregate signature scheme strongly binding
by including a collision-resistant hash of the public-key vector and the message vector in the
aggregate signature. This module defines that transform for `WordAggregateSignatureScheme` with a
keyed hash family `H`: the system parameter becomes the pair of the scheme's parameter and a hash
key `d ← setupH n`, the aggregate signature becomes `(H d (pks, ms), sigAg)`, and verification
also checks the hash. The pair `(pks, ms)` is hashed through the injective encoding
`encPair (encList encBits) (encList encBits)`.

Only correctness of the transform is proved here (`appendHash_correctOn`). Neither security
statement of the exercise is proved: strong binding of `appendHash` from collision resistance of
`H`, and `ASIG` of `appendHash` from `ASIG` of the underlying scheme. The tests show only that the
constant-hash transform of a scheme whose verifiers accept everything is not strongly binding
(`not_strongBinding_constantHash`).

## Main definitions

* `Cslib.Crypto.WordAggregateSignatureScheme.appendHash`: the scheme `SA'` of Exercise 15.11(c).

## Main results

* `Cslib.Crypto.WordAggregateSignatureScheme.appendHash_correctOn`: the transform preserves
  correctness.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Exercise 15.11(c), p. 675.
-/

public section

namespace Cslib.Crypto.WordAggregateSignatureScheme

open Probability Turing.MultiTapeTM

/-- Hashing a computed word under a computed key is computable in polynomial time, for any input
encoding. -/
private theorem computableInPolyTime_hash_comp {Param : Type} {Digest : Param → Type}
    {encParam : Param ↪ List Bool} {encDigest : (d : Param) → Digest d ↪ List Bool}
    {H : (d : Param) → List Bool → Digest d}
    (hH : ComputableInPolyTime (fun p : Param × List Bool => encDigest p.1 (H p.1 p.2))
      (encPair encParam encBits) encBits)
    {α : Type} {encIn : α ↪ List Bool} {key : α → Param} {word : α → List Bool}
    (hkey : ComputableInPolyTime key encIn encParam)
    (hword : ComputableInPolyTime word encIn encBits) :
    ComputableInPolyTime (fun a => encDigest (key a) (H (key a) (word a))) encIn encBits :=
  hH.comp (hkey.prod hword)

/-- The scheme `SA'` of Exercise 15.11(c) ([BonehShoup2023], p. 675): the system parameter is the
encoded pair of the parameter of `S` and a hash key `d ← setupH n`; the aggregate signature is the
encoded pair `(H d (pks, ms), sigAg)` of a hash of the encoded key and message vectors and an
aggregate signature of `S`; verification checks the hash and verifies `sigAg` under `S`. -/
@[expose]
def appendHash (S : WordAggregateSignatureScheme) {Param : Type} {Digest : Param → Type}
    (encParam : Param ↪ List Bool) (decParam : Decoder encParam)
    (encDigest : (d : Param) → Digest d ↪ List Bool)
    (setupH : ℕ → ProbComp Param) (hsetupH : IsPPTOn encUnary encParam setupH)
    (H : (d : Param) → List Bool → Digest d)
    (hH : ComputableInPolyTime (fun p : Param × List Bool => encDigest p.1 (H p.1 p.2))
      (encPair encParam encBits) encBits) :
    WordAggregateSignatureScheme where
  setup n := do
    let param ← S.setup n
    let d ← setupH n
    return encPair encBits encParam (param, d)
  setup_ppt := by ppt
  base := S.base
  aggregate param' pks ms sigs := do
    let (param, d) := (Decoder.bits.pair decParam).decode param'
    let sigAg ← S.aggregate param pks ms sigs
    let h := encDigest d (H d (encPair (encList encBits) (encList encBits) (pks, ms)))
    return encPair encBits encBits (h, sigAg)
  aggregate_ppt := by
    have hdec := (Decoder.bits.pair decParam).computableInPolyTime
    have hhash := @computableInPolyTime_hash_comp _ _ _ _ _ hH
    ppt
  aggregateVerify param' pks ms sigAg' :=
    let (param, d) := (Decoder.bits.pair decParam).decode param'
    let (h, sigAg) := (Decoder.bits.pair Decoder.bits).decode sigAg'
    (h == encDigest d (H d (encPair (encList encBits) (encList encBits) (pks, ms)))) &&
      S.aggregateVerify param pks ms sigAg
  aggregateVerify_polyTime := by
    have hdecP := (Decoder.bits.pair decParam).computableInPolyTime
    have hdecS := (Decoder.bits.pair Decoder.bits).computableInPolyTime
    have hhash := @computableInPolyTime_hash_comp _ _ _ _ _ hH
    polytime

/-- The transform of Exercise 15.11(c) preserves correctness, for every predicate on the vector
lengths. -/
theorem appendHash_correctOn (S : WordAggregateSignatureScheme) {Param : Type}
    {Digest : Param → Type} (encParam : Param ↪ List Bool) (decParam : Decoder encParam)
    (encDigest : (d : Param) → Digest d ↪ List Bool)
    (setupH : ℕ → ProbComp Param) (hsetupH : IsPPTOn encUnary encParam setupH)
    (H : (d : Param) → List Bool → Digest d)
    (hH : ComputableInPolyTime (fun p : Param × List Bool => encDigest p.1 (H p.1 p.2))
      (encPair encParam encBits) encBits)
    {bound : ℕ → ℕ → Prop} (hS : S.CorrectOn bound) :
    (S.appendHash encParam decParam encDigest setupH hsetupH H hH).CorrectOn bound := by
  intro n param' hparam' pks ms sigs h₁ h₂ hb hv sigAg' hmem
  simp only [appendHash, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff] at hparam' hmem
  rcases hparam' with ⟨param, hparam, d, _, rfl⟩
  simp only [Decoder.decode_enc] at hmem
  rcases hmem with ⟨sigAg, hsigAg, rfl⟩
  dsimp only [appendHash]
  simp only [Decoder.decode_enc, beq_self_eq_true, Bool.true_and]
  exact hS n param hparam pks ms sigs h₁ h₂ hb hv sigAg hsigAg

end Cslib.Crypto.WordAggregateSignatureScheme
