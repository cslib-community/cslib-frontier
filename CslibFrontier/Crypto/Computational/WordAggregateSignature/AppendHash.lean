/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import CslibFrontier.Crypto.Computational.WordAggregateSignature
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Probability.PMF

/-!
# Appending a hash of the keys and messages to an aggregate signature

Exercise 15.11(c) of [BonehShoup2023] (p. 675) makes an aggregate signature scheme strongly binding
by including a collision-resistant hash of the public-key vector and the message vector in the
aggregate signature. This module defines that transform for `WordAggregateSignatureScheme` with a
keyed hash family `H`: the system parameter becomes the pair of the scheme's parameter and a hash
key `d ← setupH n`, the aggregate signature becomes `(H d (pks, ms), sigAg)`, and verification
also checks the hash. The pair `(pks, ms)` is hashed through the injective encoding
`encPair (encList encBits) (encList encBits)`.

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
  setup_ppt := by
    refine S.setup_ppt.bind_with ?_
    have h1 : IsPPTOn (encPair encUnary encBits) encParam (fun p : ℕ × List Bool => setupH p.1) :=
      hsetupH.preprocess (ComputableInPolyTime.fst _ _)
    have h2 : ComputableInPolyTime
        (fun q : (ℕ × List Bool) × Param => encPair encBits encParam (q.1.2, q.2))
        (encPair (encPair encUnary encBits) encParam) encBits :=
      ComputableInPolyTime.encoding_comp (output := encPair encBits encParam)
        ((ComputableInPolyTime.fst _ _).snd'.prod (ComputableInPolyTime.snd _ _))
    simpa only [bind_pure_comp] using h1.map_with h2
  base := S.base
  aggregate param' pks ms sigs := do
    let (param, d) := (Decoder.bits.pair decParam).decode param'
    let sigAg ← S.aggregate param pks ms sigs
    let h := encDigest d (H d (encPair (encList encBits) (encList encBits) (pks, ms)))
    return encPair encBits encBits (h, sigAg)
  aggregate_ppt := by
    let encRest := encPair (encList encBits) (encPair (encList encBits) (encList encBits))
    let encT := encPair encBits encRest
    have hdec : ComputableInPolyTime (Decoder.bits.pair decParam).decode encBits
        (encPair encBits encParam) :=
      (Decoder.bits.pair decParam).computableInPolyTime
    have hpre : ComputableInPolyTime
        (fun t => (((Decoder.bits.pair decParam).decode t.1).1, t.2.1, t.2.2.1, t.2.2.2))
        encT encT := by
      have hp : ComputableInPolyTime
          (fun t : List Bool × List (List Bool) × List (List Bool) × List (List Bool) =>
            ((Decoder.bits.pair decParam).decode t.1).1)
          encT encBits :=
        (hdec.comp (ComputableInPolyTime.fst encBits encRest)).fst'
      exact hp.prod (ComputableInPolyTime.snd encBits encRest)
    have h1 := S.aggregate_ppt.preprocess hpre
    have hmsg : ComputableInPolyTime
        (fun q : (List Bool × List (List Bool) × List (List Bool) × List (List Bool)) × List Bool =>
          encPair (encList encBits) (encList encBits) (q.1.2.1, q.1.2.2.1))
        (encPair encT encBits) encBits :=
      ComputableInPolyTime.encoding_comp (output := encPair (encList encBits) (encList encBits))
        (by fun_prop)
    have hkey : ComputableInPolyTime
        (fun q : (List Bool × List (List Bool) × List (List Bool) × List (List Bool)) × List Bool =>
          ((Decoder.bits.pair decParam).decode q.1.1).2)
        (encPair encT encBits) encParam :=
      (hdec.comp (ComputableInPolyTime.fst encT encBits).fst').snd'
    have hdig : ComputableInPolyTime
        (fun q : (List Bool × List (List Bool) × List (List Bool) × List (List Bool)) × List Bool =>
          encDigest ((Decoder.bits.pair decParam).decode q.1.1).2
            (H ((Decoder.bits.pair decParam).decode q.1.1).2
              (encPair (encList encBits) (encList encBits) (q.1.2.1, q.1.2.2.1))))
        (encPair encT encBits) encBits :=
      hH.comp (hkey.prod hmsg)
    have h2 : ComputableInPolyTime
        (fun q : (List Bool × List (List Bool) × List (List Bool) × List (List Bool)) × List Bool =>
          encPair encBits encBits
            (encDigest ((Decoder.bits.pair decParam).decode q.1.1).2
              (H ((Decoder.bits.pair decParam).decode q.1.1).2
                (encPair (encList encBits) (encList encBits) (q.1.2.1, q.1.2.2.1))),
              q.2))
        (encPair encT encBits) encBits :=
      ComputableInPolyTime.encoding_comp (output := encPair encBits encBits)
        (hdig.prod (ComputableInPolyTime.snd _ _))
    simpa only [bind_pure_comp] using h1.map_with h2
  aggregateVerify param' pks ms sigAg' :=
    let (param, d) := (Decoder.bits.pair decParam).decode param'
    let (h, sigAg) := (Decoder.bits.pair Decoder.bits).decode sigAg'
    (h == encDigest d (H d (encPair (encList encBits) (encList encBits) (pks, ms)))) &&
      S.aggregateVerify param pks ms sigAg
  aggregateVerify_polyTime := by
    let encT := encPair encBits (encPair (encList encBits) (encPair (encList encBits) encBits))
    have hdecP : ComputableInPolyTime (Decoder.bits.pair decParam).decode encBits
        (encPair encBits encParam) :=
      (Decoder.bits.pair decParam).computableInPolyTime
    have hdecS : ComputableInPolyTime (Decoder.bits.pair Decoder.bits).decode encBits
        (encPair encBits encBits) :=
      (Decoder.bits.pair Decoder.bits).computableInPolyTime
    have hparam : ComputableInPolyTime
        (fun t : List Bool × List (List Bool) × List (List Bool) × List Bool =>
          ((Decoder.bits.pair decParam).decode t.1).1)
        encT encBits :=
      (hdecP.comp (ComputableInPolyTime.fst _ _)).fst'
    have hkey : ComputableInPolyTime
        (fun t : List Bool × List (List Bool) × List (List Bool) × List Bool =>
          ((Decoder.bits.pair decParam).decode t.1).2)
        encT encParam :=
      (hdecP.comp (ComputableInPolyTime.fst _ _)).snd'
    have hh : ComputableInPolyTime
        (fun t : List Bool × List (List Bool) × List (List Bool) × List Bool =>
          ((Decoder.bits.pair Decoder.bits).decode t.2.2.2).1)
        encT encBits :=
      (hdecS.comp (by fun_prop)).fst'
    have hsigAg : ComputableInPolyTime
        (fun t : List Bool × List (List Bool) × List (List Bool) × List Bool =>
          ((Decoder.bits.pair Decoder.bits).decode t.2.2.2).2)
        encT encBits :=
      (hdecS.comp (by fun_prop)).snd'
    have hmsg : ComputableInPolyTime
        (fun t : List Bool × List (List Bool) × List (List Bool) × List Bool =>
          encPair (encList encBits) (encList encBits) (t.2.1, t.2.2.1))
        encT encBits :=
      ComputableInPolyTime.encoding_comp (output := encPair (encList encBits) (encList encBits))
        (by fun_prop)
    have hdig := hH.comp (hkey.prod hmsg)
    have hV := S.aggregateVerify_polyTime.comp
      (hparam.prod ((by fun_prop : ComputableInPolyTime (fun t => t.2.1) encT _).prod
        ((by fun_prop : ComputableInPolyTime (fun t => t.2.2.1) encT _).prod hsigAg)))
    fun_prop

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
