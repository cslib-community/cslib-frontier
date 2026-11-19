/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.LinearSigmaProtocol
public import CslibFrontier.Crypto.Computational.SchnorrIdentification
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Efficient.Verifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.ZMod.NatCast
import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.PPT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip

/-!
# Schnorr's Sigma protocol with an efficient prover, verifier, extractor and simulator

Schnorr's Sigma protocol ([BonehShoup2023], Example 19.1) over a `PrimeOrderGroupFamily`, as a
family indexed by a unary security parameter `n` and a group description `d`, with challenges in
`ZMod q` for the group order `q`. Group elements are encoded by the family's encoding and scalars
in binary (`schnorrEncoding`).

Two protocol families share the same response function, verifier (`encodeSchnorrVerify`,
`efficientVerifier_schnorr`, `efficientVerifier_schnorrProb`) and extractor (`schnorrExtract`):

* `schnorrFamily` draws its commitment nonce `αₜ` from the exact uniform distribution on `ZMod q`
  at the `PMF` level (`SigmaProtocol.linear`), an ideal sampler that no strict-PPT fair-coin
  machine realizes with zero error when `q` is not a power of two. The zero-knowledge theorems for
  `schnorrFamily` (`efficientSpecialHVZK_schnorr_ideal`, `computationalSpecialHVZK_schnorr_ideal`)
  are therefore ideal-sampling steps toward Example 19.3, consumed by the fair-coin theorems below.
* `schnorrProbFamily` specializes `linearProbFamily` (`SigmaProtocol.linear` with its commitment
  nonce drawn from fair coins by `sampleExp`, within `1 / 2 ^ n` of uniform on `ZMod q`). On
  encodings, its commitment and state `(r • g, r)` are sampled in uniform strict PPT by
  `schnorrSigKeyGen` (`eval_schnorrSigKeyGen_eq_schnorrProbCommit`, `isPPTOn_schnorrSigKeyGen`) and
  its response `r + c * α` is computed in deterministic polynomial time by `schnorrRespondBits`
  (`computableInPolyTime_schnorrRespondBits`, `schnorrRespondBits_schnorrProbFamily`).

Main results for the protocol:

* **Completeness** (`schnorrProbFamily_complete`, Example 19.1 with Definition 19.3): every honest
  execution of `schnorrProbFamily` on a valid pair `(α, u)` accepts at every challenge.
* **Efficient verification and special soundness** (`efficientVerifier_schnorrProb`,
  `efficientSpecialSoundness_schnorr`, `efficientSpecialSoundness_schnorrProb`, Example 19.2 with
  Definition 19.4): `encodeSchnorrVerify` decides `z • g = t + c • u` in polynomial time, and
  `schnorrExtract` computes `(c - c')⁻¹ (z - z')` with `extractNat`, inverting by Fermat's little
  theorem, in polynomial time (`schnorrExtractWord`).
* **Statistical and computational special HVZK for the fair-coin prover**
  (`closeTo_transcript_schnorrProbFamily_simulator`, `advantage_chvzkGame_schnorrProbFamily_le`,
  `computationalSpecialHVZK_schnorr`, Example 19.3 with Definitions 19.5 and 20.6): Example 19.3
  states exact special HVZK (Definition 19.5(ii), under Definition 2.8's negligible-overflow
  runtime convention on p. 30). Because exact simulation on `ZMod q` is impossible in the
  strict-PPT fair-coin model when `q` is not a power of two, Definition 19.5(ii) is relaxed here to
  `2 / 2 ^ n` statistical transcript closeness (`1 / 2 ^ n` from the prover's `sampleExp`
  commitment nonce and `1 / 2 ^ n` from `schnorrSimulator`'s `sampleExp` response), `2 / 2 ^ n`
  distinguishing advantage in Attack Game 20.4 against arbitrary (even computationally unbounded)
  adversaries, and Definition 20.6 (`ComputationalSpecialHVZK`) with exact zero acceptance error
  (`accepts_schnorrSimulator`, `δ = fun _ => 0`), derived without proof duplication through the
  shared `linearProbFamily` transfer in `CslibFrontier.Crypto.Computational.LinearSigmaProtocol`.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrFamily`: Schnorr's Sigma protocol with an ideal
  `ZMod q` commitment sampler.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrProbCommit`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrProbFamily`: Schnorr's Sigma protocol with a fair-coin
  `sampleExp` commitment sampler.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrBitSigma`: Schnorr's Sigma protocol in one group with
  `m`-bit challenges.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrEncoding`: its word encodings.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrExtract`, `schnorrExtractWord`: the extractor,
  computed with `extractNat`, and the word function computing it on encodings.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrSampleChallenge`: a fair-coin challenge sampler
  within `1 / 2 ^ n` of uniform on `ZMod q`.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrSimulator`: the simulator with `sampleExp`.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrSimulateWord`: the simulator as a strict PPT program
  on words.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrIdealKeyGen`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrSigKeyGen`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrCommitBits`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encSchnorrBitsInput`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrRespondBits`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrRecoverCommitBits`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encodeSchnorrVerify`: shared bit-encoded Schnorr key
  generation, commitment, response, commitment recovery, and verification.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrProbFamily_complete`: completeness of
  `schnorrProbFamily` (Definition 19.3).
* `Cslib.Crypto.PrimeOrderGroupFamily.efficientSpecialSoundness_schnorr`,
  `Cslib.Crypto.PrimeOrderGroupFamily.efficientSpecialSoundness_schnorrProb`: efficient special
  soundness (Example 19.2), with `schnorrExtractWord` as its polynomial-time word function.
* `Cslib.Crypto.PrimeOrderGroupFamily.verifierRealizedBy_encodeSchnorrVerify`,
  `Cslib.Crypto.PrimeOrderGroupFamily.efficientVerifier_schnorr`,
  `Cslib.Crypto.PrimeOrderGroupFamily.efficientVerifier_schnorrProb`: deterministic polynomial-time
  verification on encodings.
* `Cslib.Crypto.PrimeOrderGroupFamily.eval_schnorrSigKeyGen_eq_schnorrProbCommit`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrRespondBits_schnorrProbFamily`: word-level
  realizations of `schnorrProbFamily`'s commitment and response by `schnorrSigKeyGen` and
  `schnorrRespondBits`.
* `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_schnorrSampleChallenge`,
  `Cslib.Crypto.PrimeOrderGroupFamily.closeTo_schnorrSampleChallenge`: the challenge sampler is
  strict PPT and `1 / 2 ^ n`-close to uniform.
* `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_schnorrSimulateWord`,
  `Cslib.Crypto.PrimeOrderGroupFamily.eval_schnorrSimulateWord`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_schnorrSimulator`,
  `Cslib.Crypto.PrimeOrderGroupFamily.simulatorRealizedBy_schnorrSimulator`: the word program is
  strict PPT and computes `schnorrSimulator` on encodings, so `schnorrSimulator` is strict PPT; it
  realizes Boneh and Shoup's simulator up to `1 / 2 ^ n`.
* `Cslib.Crypto.PrimeOrderGroupFamily.accepts_schnorrSimulator`: exact acceptance (`δ = 0`).
* `Cslib.Crypto.PrimeOrderGroupFamily.closeTo_transcript_schnorrProbFamily_simulator`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_chvzkGame_schnorrProbFamily_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computationalSpecialHVZK_schnorr`: `2 / 2 ^ n` transcript
  closeness, Attack Game 20.4 advantage bound against arbitrary adversaries, and Definition 20.6
  computational special HVZK with zero acceptance error for the fair-coin `schnorrProbFamily`.
* `Cslib.Crypto.PrimeOrderGroupFamily.eval_schnorrSigKeyGen`,
  `Cslib.Crypto.PrimeOrderGroupFamily.closeTo_schnorrSigKeyGen`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_schnorrSigKeyGen_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_schnorrSigKeyGen`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_schnorrCommitBits`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_schnorrRespondBits`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_schnorrRecoverCommitBits`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encodeSchnorrVerify_encode`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encodeSchnorrVerify_eq_true_iff`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_encodeSchnorrVerify`: strict-PPT and
  polynomial-time certificates and canonical-key characterizations for the shared bit-encoded
  Schnorr operations.

## Ideal-sampling steps toward Example 19.3

* `Cslib.Crypto.PrimeOrderGroupFamily.efficientSpecialHVZK_schnorr_ideal`: efficient special HVZK
  with statistical error `1 / 2 ^ n`, against the ideal-sampling prover.
* `Cslib.Crypto.PrimeOrderGroupFamily.computationalSpecialHVZK_schnorr_ideal`: computational
  special HVZK (Definition 20.6) with zero acceptance error, against the ideal-sampling prover.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Definition 2.8 (p. 30), Figure 19.1 (p. 756), Definitions 19.3–19.5
  and Examples 19.1–19.3 (pp. 772–774), and Attack Game 20.4 and Definition 20.6 (p. 840).
* [C.-P. Schnorr, *Efficient Signature Generation by Smart Cards*][Schnorr1991]
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Protocols Protocols.SigmaProtocol Interactive
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)

/-- Group elements as words, through the family's injective encoding. -/
def encodeEmbedding (d : F.Desc) : F.Carrier d ↪ List Bool :=
  ⟨F.encode d, F.encode_injective d⟩

/-- Scalars modulo the group order as binary numbers, through their least nonnegative
representatives. -/
def encScalar (d : F.Desc) : ZMod (F.order d) ↪ List Bool :=
  ⟨fun a => encNat a.val, encNat.injective.comp (ZMod.val_injective _)⟩

/-- Schnorr's Sigma protocol ([BonehShoup2023], Example 19.1) in the group described by `i.2`,
with challenges in `ZMod q`. The security parameter `i.1` does not change the protocol. The honest
prover draws its commitment nonce exactly uniformly on `ZMod q` at the `PMF` level, an ideal
sampler that no fair-coin machine with a strict polynomial time bound realizes exactly when `q` is
not a power of two; see `schnorrProbFamily` for the fair-coin `sampleExp` prover. -/
noncomputable def schnorrFamily (i : ℕ × F.Desc) :
    SigmaProtocol (ZMod (F.order i.2)) (F.Carrier i.2) (F.Carrier i.2) (ZMod (F.order i.2))
      (ZMod (F.order i.2)) :=
  schnorr (Function.Embedding.refl _) (F.generator i.2)

/-- Fair-coin commitment sampler for Schnorr's Sigma protocol ([BonehShoup2023], Figure 19.1,
p. 756, and Example 19.1, p. 773): at index `i = (n, d)`, draw `s ← F.sampleExp n d`, read
`r = s mod q`, and return `(r • g, r)`. -/
noncomputable def schnorrProbCommit :
    ∀ i : ℕ × F.Desc, ZMod (F.order i.2) → F.Carrier i.2 →
      ProbComp (F.Carrier i.2 × ZMod (F.order i.2)) :=
  F.linearProbCommit fun i _ =>
    LinearMap.toSpanSingleton (ZMod (F.order i.2)) (F.Carrier i.2) (F.generator i.2)

/-- Schnorr's Sigma protocol ([BonehShoup2023], Figure 19.1, p. 756, and Example 19.1, p. 773) with
a fair-coin commitment sampler: at index `i = (n, d)`, the honest prover commits with
`schnorrProbCommit i` (`sampleExp n d`), responds with `r + c * α`, and the verifier checks
`z • g = t + c • u`. -/
noncomputable def schnorrProbFamily :
    ∀ i : ℕ × F.Desc,
      SigmaProtocol (ZMod (F.order i.2)) (F.Carrier i.2) (F.Carrier i.2) (ZMod (F.order i.2))
        (ZMod (F.order i.2)) :=
  F.linearProbFamily
    (fun i _ => LinearMap.toSpanSingleton (ZMod (F.order i.2)) (F.Carrier i.2) (F.generator i.2))
    (fun _ => id) (fun _ => Function.Embedding.refl _)

/-- Schnorr's Sigma protocol in `F.Carrier d` with `m`-bit challenges `BitString m`, embedded as
scalars by `challengeEmbedding` when `2 ^ m ≤ F.order d`. -/
noncomputable def schnorrBitSigma (d : F.Desc) {m : ℕ} (hm : 2 ^ m ≤ F.order d) :
    SigmaProtocol (ZMod (F.order d)) (F.Carrier d) (F.Carrier d) (BitString m)
      (ZMod (F.order d)) :=
  schnorr (F.challengeEmbedding d hm) (F.generator d)

/-- The word encodings of `schnorrFamily`: the unary security parameter with the description,
group elements by the family's encoding, and challenges and responses in binary. -/
def schnorrEncoding :
    Encoding (ℕ × F.Desc) (fun i => F.Carrier i.2) (fun i => F.Carrier i.2)
      (fun i => ZMod (F.order i.2)) (fun i => ZMod (F.order i.2)) where
  index := encPair encUnary F.encDesc
  statement i := F.encodeEmbedding i.2
  commitment i := F.encodeEmbedding i.2
  challenge i := F.encScalar i.2
  response i := F.encScalar i.2

/-- Schnorr's extractor ([BonehShoup2023], Example 19.2), computed with `extractNat`: it is
`(c - c')⁻¹ (z - z')` whenever `c ≠ c'`. -/
def schnorrExtract (i : ℕ × F.Desc) (_ _ : F.Carrier i.2) (c z c' z' : ZMod (F.order i.2)) :
    ZMod (F.order i.2) :=
  extractNat (F.order i.2) c.val z.val c'.val z'.val

/-- Schnorr's extractor on words: on the index `(n, d)` and the binary challenges and responses of
two conversations, return `extractNat` of their values in binary. It computes `schnorrExtract` on
encodings (`extractorRealizedBy_schnorrExtractWord`). -/
def schnorrExtractWord :
    (ℕ × F.Desc) × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool →
      List Bool
  | ((_, d), _, _, c, z, c', z') =>
    (extractNat (F.order d) (ofBits c) (ofBits z) (ofBits c') (ofBits z')).bits

/-- Schnorr's simulator ([BonehShoup2023], Example 19.3) with fair coins: at index `(n, d)`, on a
statement `u` and a challenge `c`, sample `s` with `sampleExp n d`, read it as the response
`z = s mod q`, and return the commitment `z • g - c • u` with `z`. -/
noncomputable def schnorrSimulator :
    Simulator (ℕ × F.Desc) (fun i => F.Carrier i.2) (fun i => F.Carrier i.2)
      (fun i => ZMod (F.order i.2)) (fun i => ZMod (F.order i.2)) :=
  fun i u c => (fun z => (z • F.generator i.2 - c • u, z)) <$>
    ((Nat.cast : ℕ → ZMod (F.order i.2)) <$> F.sampleExp i.1 i.2)

/-- Schnorr's simulator on words ([BonehShoup2023], Example 19.3): on the index `(n, d)`, an
encoded statement `u` and a binary challenge `c`, sample `s` with `sampleExp n d` and return the
encodings of `s • g - c • u` and of `s mod q`. It is the strict PPT certificate of
`schnorrSimulator` (`eval_schnorrSimulateWord`); `SchnorrEavesdrop` also runs it on arbitrary
challenge words. -/
noncomputable def schnorrSimulateWord :
    (ℕ × F.Desc) × List Bool × List Bool → ProbComp (List Bool × List Bool)
  | ((n, d), u, c) => do
    let s ← F.sampleExp n d
    return (F.add (d, F.smul (d, s, F.encode d (F.generator d)),
        F.smul (d, F.order d - ofBits c % F.order d, u)),
      (s % F.order d).bits)

/-! ### Special soundness -/

/-- `schnorrExtractWord` is computable in polynomial time. -/
theorem computableInPolyTime_schnorrExtractWord :
    ComputableInPolyTime F.schnorrExtractWord (encPair (encPair encUnary F.encDesc)
      (encPair encBits (encPair encBits (encPair encBits (encPair encBits
        (encPair encBits encBits)))))) encBits := by
  let encIn := encPair (encPair encUnary F.encDesc) (encPair encBits (encPair encBits
    (encPair encBits (encPair encBits (encPair encBits encBits)))))
  have hd : ComputableInPolyTime
      (fun p : (ℕ × F.Desc) × List Bool × List Bool × List Bool × List Bool × List Bool ×
        List Bool => p.1.2) encIn F.encDesc := by fun_prop
  have hword {k : (ℕ × F.Desc) × List Bool × List Bool × List Bool × List Bool × List Bool ×
      List Bool → List Bool} (hk : ComputableInPolyTime k encIn encBits) :
      ComputableInPolyTime (fun p => ofBits (k p)) encIn encNat :=
    (ComputableInPolyTime.bitsToNat.comp hk)
  have hext := computableInPolyTime_extractNat hd
    (hword (k := fun p => p.2.2.2.1) (by fun_prop))
    (hword (k := fun p => p.2.2.2.2.1) (by fun_prop))
    (hword (k := fun p => p.2.2.2.2.2.1) (by fun_prop))
    (hword (k := fun p => p.2.2.2.2.2.2) (by fun_prop))
  exact hext.encoding_comp

/-- `schnorrExtractWord` computes Schnorr's extractor `schnorrExtract` on encodings. -/
theorem extractorRealizedBy_schnorrExtractWord :
    ExtractorRealizedBy F.schnorrEncoding (fun i => F.encScalar i.2) F.schnorrExtract
      F.schnorrExtractWord := by
  intro i u t c z c' z'
  simp only [schnorrExtractWord, schnorrEncoding, encScalar, encodeEmbedding,
    Function.Embedding.coeFn_mk, encNat_apply, ofBits_bits, schnorrExtract, ZMod.val_natCast,
    extractNat, Nat.mod_mod]

/-- **Schnorr's protocol has efficient special soundness** ([BonehShoup2023], Example 19.2). -/
theorem efficientSpecialSoundness_schnorr :
    EfficientSpecialSoundness F.schnorrFamily (fun i α u => α • F.generator i.2 = u)
      F.schnorrEncoding (fun i => F.encScalar i.2) F.schnorrExtract where
  specialSoundness i u t c z c' z' hc hz hz' := by
    have h := schnorr_specialSoundness (ι := Function.Embedding.refl _) u t c z c' z' hc hz hz'
    simp only [linearExtract, Function.Embedding.refl_apply, smul_eq_mul] at h
    simpa only [schnorrExtract, extractNat_zmod_val hc] using h
  polyTime := ⟨F.schnorrExtractWord, F.computableInPolyTime_schnorrExtractWord,
    F.extractorRealizedBy_schnorrExtractWord⟩

/-! ### Special HVZK -/

/-- A challenge sampler for `schnorrFamily` with fair coins: at index `(n, d)`, sample `s` with
`sampleExp n d` and read it modulo the group order. It is within statistical distance `1 / 2 ^ n`
of uniform (`closeTo_schnorrSampleChallenge`). -/
noncomputable def schnorrSampleChallenge (i : ℕ × F.Desc) : ProbComp (ZMod (F.order i.2)) :=
  (Nat.cast : ℕ → ZMod (F.order i.2)) <$> F.sampleExp i.1 i.2

/-- One machine samples the encoded challenges of `schnorrSampleChallenge` from the encoded index:
it samples `s` with `sampleExp n d` and writes the binary encoding of `s mod q`. -/
theorem isPPTOn_schnorrSampleChallenge :
    IsPPTOn (encPair encUnary F.encDesc) encBits
      fun i => F.schnorrEncoding.challenge i <$> F.schnorrSampleChallenge i := by
  let encIdx := encPair encUnary F.encDesc
  have hn : ComputableInPolyTime (fun i : ℕ × F.Desc => i.1) encIdx encUnary := by fun_prop
  have hd : ComputableInPolyTime (fun i : ℕ × F.Desc => i.2) encIdx F.encDesc := by fun_prop
  have hword : IsPPTOn encIdx encBits fun i => F.sampleExp i.1 i.2 >>= fun s =>
      pure (s % F.order i.2).bits := by
    refine (F.isPPTOn_sampleExp hn hd).bind_with ?_
    let encMid := encPair encIdx encNat
    have hd' : ComputableInPolyTime (fun p : (ℕ × F.Desc) × ℕ => p.1.2) encMid F.encDesc := by
      fun_prop
    have hs : ComputableInPolyTime (fun p : (ℕ × F.Desc) × ℕ => p.2) encMid encNat := by
      fun_prop
    have hq := F.computableInPolyTime_order.comp hd'
    have hz : ComputableInPolyTime (fun p : (ℕ × F.Desc) × ℕ => (p.2 % F.order p.1.2).bits)
        encMid encBits :=
      .of_tidy (ComputableTidilyInPolyTime.natBits.comp (.binary_mod' hs.tidy hq.tidy))
    exact hz.isPPTOn
  refine hword.congr fun i => ?_
  rw [schnorrSampleChallenge, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_map,
    PMF.map_comp]
  simp only [ProbComp.eval_pure]
  rw [← PMF.bind_pure_comp]
  congr 1 with s : 1
  simp only [Function.comp_apply, schnorrEncoding, encScalar, Function.Embedding.coeFn_mk,
    encNat_apply, ZMod.val_natCast]

/-- `schnorrSampleChallenge` is within statistical distance `1 / 2 ^ n` of uniform on
`ZMod q`. -/
theorem closeTo_schnorrSampleChallenge (i : ℕ × F.Desc) :
    CloseTo (PMF.uniformOfFintype (ZMod (F.order i.2)))
      (ProbComp.eval (F.schnorrSampleChallenge i)) (1 / 2 ^ i.1 : ℝ≥0) := by
  rw [schnorrSampleChallenge, ProbComp.eval_map]
  exact F.closeTo_uniform_sampleExp i.1 i.2

/-- On an encoded statement and challenge, `schnorrSimulateWord` computes the encoded output of
`schnorrSimulator`. -/
theorem eval_schnorrSimulateWord (i : ℕ × F.Desc) (u : F.Carrier i.2) (c : ZMod (F.order i.2)) :
    ProbComp.eval (F.schnorrSimulateWord
        (i, F.schnorrEncoding.statement i u, F.schnorrEncoding.challenge i c)) =
      (ProbComp.eval (F.schnorrSimulator i u c)).map
        (Prod.map (F.schnorrEncoding.commitment i) (F.schnorrEncoding.response i)) := by
  obtain ⟨n, d⟩ := i
  have hneg : ((F.order d - c.val % F.order d : ℕ) : ZMod (F.order d)) = -c := by
    rw [ZMod.natCast_sub_mod_eq_neg, ZMod.natCast_zmod_val]
  rw [show (F.schnorrEncoding.statement (n, d)) u = F.encode d u from rfl,
    show (F.schnorrEncoding.challenge (n, d)) c = encNat c.val from rfl,
    schnorrSimulateWord, ProbComp.eval_bind, schnorrSimulator, ProbComp.eval_map,
    ProbComp.eval_map, PMF.map_comp, PMF.map_comp]
  simp only [ProbComp.eval_pure, encNat_apply, ofBits_bits, F.smul_encode, F.add_encode, hneg,
    neg_smul, ← sub_eq_add_neg]
  rw [← PMF.bind_pure_comp]
  congr 1 with a : 1
  simp only [Function.comp_apply, Prod.map, schnorrEncoding, encodeEmbedding, encScalar,
    Function.Embedding.coeFn_mk, encNat_apply, ZMod.val_natCast]

/-- A word-level commitment step `k • b + (q - c % q) • x` computed with the family's word
operations is computable in polynomial time from polynomial-time components. -/
theorem computableInPolyTime_add_smul_sub_mod {α : Type} {encIn : α ↪ List Bool}
    {d : α → F.Desc} {k : α → ℕ} {b c x : α → List Bool}
    (hd : ComputableInPolyTime d encIn F.encDesc)
    (hk : ComputableInPolyTime k encIn encNat)
    (hb : ComputableInPolyTime b encIn encBits)
    (hc : ComputableInPolyTime c encIn encBits)
    (hx : ComputableInPolyTime x encIn encBits) :
    ComputableInPolyTime
      (fun p => F.add (d p, F.smul (d p, k p, b p),
        F.smul (d p, F.order (d p) - ofBits (c p) % F.order (d p), x p)))
      encIn encBits := by
  have hq := F.computableInPolyTime_order.comp hd
  have hneg : ComputableInPolyTime
      (fun p => F.order (d p) - ofBits (c p) % F.order (d p)) encIn encNat :=
    .binary_sub' hq (.binary_mod' (ComputableInPolyTime.bitsToNat.comp hc) hq)
  exact F.computableInPolyTime_add.comp
    (hd.prod ((F.computableInPolyTime_smul.comp (hd.prod (hk.prod hb))).prod
      (F.computableInPolyTime_smul.comp (hd.prod (hneg.prod hx)))))

/-- `schnorrSimulateWord` is uniform strict PPT in the security parameter, the description and the
encoded statement and challenge. -/
theorem isPPTOn_schnorrSimulateWord :
    IsPPTOn (encPair (encPair encUnary F.encDesc) (encPair encBits encBits))
      (encPair encBits encBits) F.schnorrSimulateWord := by
  let encIn := encPair (encPair encUnary F.encDesc) (encPair encBits encBits)
  have hn : ComputableInPolyTime (fun p : (ℕ × F.Desc) × List Bool × List Bool => p.1.1)
      encIn encUnary := by fun_prop
  have hd : ComputableInPolyTime (fun p : (ℕ × F.Desc) × List Bool × List Bool => p.1.2)
      encIn F.encDesc := by fun_prop
  change IsPPTOn encIn _ fun p => F.sampleExp p.1.1 p.1.2 >>= fun s =>
    pure (F.add (p.1.2, F.smul (p.1.2, s, F.encode p.1.2 (F.generator p.1.2)),
        F.smul (p.1.2, F.order p.1.2 - ofBits p.2.2 % F.order p.1.2, p.2.1)),
      (s % F.order p.1.2).bits)
  refine (F.isPPTOn_sampleExp hn hd).bind_with ?_
  let encMid := encPair encIn encNat
  have hd' : ComputableInPolyTime (fun p : ((ℕ × F.Desc) × List Bool × List Bool) × ℕ =>
      p.1.1.2) encMid F.encDesc := by fun_prop
  have hs : ComputableInPolyTime (fun p : ((ℕ × F.Desc) × List Bool × List Bool) × ℕ =>
      p.2) encMid encNat := by fun_prop
  have hu : ComputableInPolyTime (fun p : ((ℕ × F.Desc) × List Bool × List Bool) × ℕ =>
      p.1.2.1) encMid encBits := by fun_prop
  have hc : ComputableInPolyTime (fun p : ((ℕ × F.Desc) × List Bool × List Bool) × ℕ =>
      p.1.2.2) encMid encBits := by fun_prop
  have hq := F.computableInPolyTime_order.comp hd'
  have ht := F.computableInPolyTime_add_smul_sub_mod hd' hs
    (F.computableInPolyTime_generator.comp hd') hc hu
  have hz : ComputableInPolyTime
      (fun p : ((ℕ × F.Desc) × List Bool × List Bool) × ℕ =>
        (p.2 % F.order p.1.1.2).bits) encMid encBits :=
    (ComputableInPolyTime.binary_mod' hs hq).encoding_comp
  exact (ht.prod hz).isPPTOn

/-- `schnorrSimulator` is uniform strict PPT, certified by `schnorrSimulateWord`. -/
theorem isPPT_schnorrSimulator : Simulator.IsPPT F.schnorrEncoding F.schnorrSimulator :=
  .of_word F.isPPTOn_schnorrSimulateWord fun i u c => (F.eval_schnorrSimulateWord i u c).symm

/-- `schnorrSimulator` realizes Schnorr's perfect simulator `linearSimulate`
([BonehShoup2023], Example 19.3) up to statistical distance `1 / 2 ^ n` at security parameter
`n`. -/
theorem simulatorRealizedBy_schnorrSimulator :
    SimulatorRealizedBy
      (fun i : ℕ × F.Desc => linearSimulate (fun _ => LinearMap.toSpanSingleton
        (ZMod (F.order i.2)) (F.Carrier i.2) (F.generator i.2)) id (Function.Embedding.refl _))
      F.schnorrSimulator (fun i => 1 / 2 ^ i.1) :=
  fun i _ _ => F.closeTo_map_uniform_sampleExp i.1 i.2 _

/-- Ideal-sampling step toward [BonehShoup2023], Example 19.3 (special HVZK, Definition 19.5),
not the cited result: against the honest prover of `schnorrFamily`, which draws its commitment
nonce exactly uniformly on `ZMod q` at the `PMF` level, `linearSimulate` is a perfect simulator,
and the strict PPT simulator `schnorrSimulator` realizes it with statistical error `1 / 2 ^ n` at
security parameter `n`. Consumed by `closeTo_transcript_schnorrProbFamily_simulator` and
`advantage_chvzkGame_schnorrProbFamily_le` for the fair-coin prover `schnorrProbFamily`. -/
theorem efficientSpecialHVZK_schnorr_ideal :
    EfficientSpecialHVZK F.schnorrFamily (fun i α u => α • F.generator i.2 = u) F.schnorrEncoding
      (fun i => linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod (F.order i.2))
        (F.Carrier i.2) (F.generator i.2)) id (Function.Embedding.refl _))
      (fun i => 1 / 2 ^ i.1) where
  specialHVZK _ := schnorr_specialHVZK
  realized := ⟨_, F.isPPT_schnorrSimulator, F.simulatorRealizedBy_schnorrSimulator⟩

/-- Every output of `schnorrSimulator` is an accepting conversation (acceptance error `0`): for
every sampled `z`, `(z • g - c • u) + c • u = z • g`. -/
theorem accepts_schnorrSimulator (i : ℕ × F.Desc) (u : F.Carrier i.2) (c : ZMod (F.order i.2)) :
    (ProbComp.eval (F.schnorrSimulator i u c)).toOuterMeasure
      {tz | (F.schnorrFamily i).Accepts u tz.1 c tz.2} = 1 := by
  simp only [schnorrSimulator, ProbComp.eval_map, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_apply_eq_one_iff]
  intro z _
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, schnorrFamily, schnorr_accepts_iff,
    Function.Embedding.refl_apply, sub_add_cancel]

/-- Ideal-sampling step toward [BonehShoup2023], Example 19.3 with Definition 20.6 (special
computational HVZK), not the cited result: Experiment 0 of Attack Game 20.4 runs the honest prover
of `schnorrFamily`, which draws its commitment nonce exactly uniformly on `ZMod q` at the `PMF`
level, and against it the strict PPT simulator `schnorrSimulator` satisfies Definition 20.6 with
zero acceptance error (`δ = fun _ => 0`) over any group-description setup
`setup : ℕ → PMF F.Desc` paired with the security parameter. Consumed by
`computationalSpecialHVZK_schnorr` for the fair-coin prover `schnorrProbFamily`. -/
theorem computationalSpecialHVZK_schnorr_ideal (setup : ℕ → PMF F.Desc) :
    ComputationalSpecialHVZK F.schnorrFamily (fun i α u => α • F.generator i.2 = u)
      F.schnorrEncoding (fun i => F.encScalar i.2) (fun n => (setup n).map (n, ·))
      F.schnorrSimulator (fun _ => 0) :=
  F.simulatorRealizedBy_schnorrSimulator.computationalSpecialHVZK_of_accepts
    (fun _ => schnorr_specialHVZK) F.isPPT_schnorrSimulator
    (fun i u c => by rw [F.accepts_schnorrSimulator i u c, tsub_zero])
    (exists_negligible_inv_two_pow_map setup)

/-! ### Fair-coin `schnorrProbFamily` completeness, special soundness, and special HVZK -/

/-- **Completeness of the fair-coin Schnorr Sigma protocol** ([BonehShoup2023], Figure 19.1,
p. 756, and Example 19.1 with Definition 19.3, pp. 772–773): for every valid discrete-logarithm
pair `α • g = u` and every challenge `c`, every honest transcript of `schnorrProbFamily i` is
accepting. -/
theorem schnorrProbFamily_complete (i : ℕ × F.Desc) :
    (F.schnorrProbFamily i).Complete fun α u => α • F.generator i.2 = u :=
  (F.linearProbFamily_complete _ _ _ i).mono fun _ _ h => by simpa using h

/-- **Efficient special soundness of the fair-coin Schnorr Sigma protocol** ([BonehShoup2023],
Example 19.2 with Definition 19.4, p. 773): `schnorrProbFamily` shares the verifier of
`schnorrFamily`, so `schnorrExtract` (`schnorrExtractWord`) extracts `α` in polynomial time. -/
theorem efficientSpecialSoundness_schnorrProb :
    EfficientSpecialSoundness F.schnorrProbFamily (fun i α u => α • F.generator i.2 = u)
      F.schnorrEncoding (fun i => F.encScalar i.2) F.schnorrExtract :=
  F.efficientSpecialSoundness_schnorr.of_verify_eq fun _ => rfl

/-- On every valid discrete-logarithm pair `(α, u)` and challenge `c`, the honest transcript of the
fair-coin `schnorrProbFamily` and the output of the strict PPT simulator `schnorrSimulator` are
within statistical distance `2 / 2 ^ n` (`1 / 2 ^ n` from the prover's `sampleExp` commitment nonce
and `1 / 2 ^ n` from the simulator's `sampleExp` response; [BonehShoup2023], Example 19.3 with
Definition 19.5, p. 774, relaxing Definition 19.5(ii)'s identical transcript distribution to
`2 / 2 ^ n` statistical closeness in the strict-PPT fair-coin model, cf. Definition 2.8, p. 30).
Derived from `efficientSpecialHVZK_schnorr_ideal` via
`closeTo_transcript_linearProbFamily_simulator`. -/
theorem closeTo_transcript_schnorrProbFamily_simulator (i : ℕ × F.Desc)
    {α : ZMod (F.order i.2)} {u : F.Carrier i.2}
    (hxy : α • F.generator i.2 = u) (c : ZMod (F.order i.2)) :
    CloseTo ((F.schnorrProbFamily i).transcript α u c)
      (ProbComp.eval (F.schnorrSimulator i u c)) (2 / 2 ^ i.1) :=
  F.closeTo_transcript_linearProbFamily_simulator
    F.efficientSpecialHVZK_schnorr_ideal.specialHVZK F.simulatorRealizedBy_schnorrSimulator hxy c

/-- In Attack Game 20.4 (`chvzkRealGame` vs `chvzkSimGame`), the fair-coin Schnorr prover
`schnorrProbFamily` and the strict PPT simulator `schnorrSimulator` differ in distinguishing
advantage by at most `2 / 2 ^ n` against *every* adversary (including computationally unbounded
ones). Derived from `efficientSpecialHVZK_schnorr_ideal` via
`advantage_chvzkGame_linearProbFamily_le`. -/
theorem advantage_chvzkGame_schnorrProbFamily_le {σ : Type} (setup : ℕ → PMF F.Desc)
    (A : CHVZKAdversary (ℕ × F.Desc) (fun i => ZMod (F.order i.2))
      (fun i => F.Carrier i.2) (fun i => F.Carrier i.2)
      (fun i => ZMod (F.order i.2)) (fun i => ZMod (F.order i.2)) σ) (n : ℕ) :
    Game.advantage
      (chvzkRealGame F.schnorrProbFamily (fun i α u => α • F.generator i.2 = u)
        (fun m => (setup m).map (m, ·)) A n)
      (chvzkSimGame (fun i α u => α • F.generator i.2 = u)
        (fun m => (setup m).map (m, ·)) F.schnorrSimulator A n) ≤
      2 / 2 ^ n :=
  F.advantage_chvzkGame_linearProbFamily_le
    F.efficientSpecialHVZK_schnorr_ideal.specialHVZK F.simulatorRealizedBy_schnorrSimulator
    setup A n

/-- **Schnorr's fair-coin Sigma protocol satisfies computational special HVZK** ([BonehShoup2023],
Example 19.3, Section 19.4.2, p. 774, with Definition 20.6, Section 20.4.2, p. 840): Example 19.3
states exact special HVZK (Definition 19.5(ii), under Definition 2.8's negligible-overflow runtime
convention, p. 30); in the strict-PPT fair-coin model exact simulation on `ZMod q` is impossible
when `q` is not a power of two, so Definition 19.5(ii) is relaxed here to the `2 / 2 ^ n`
statistical form (`closeTo_transcript_schnorrProbFamily_simulator`) and Definition 20.6. Against
the fair-coin honest prover of `schnorrProbFamily`, the strict PPT simulator `schnorrSimulator`
satisfies Definition 20.6 with exact zero acceptance error (`δ = fun _ => 0`) over any
group-description setup `setup : ℕ → PMF F.Desc` paired with the security parameter. Derived from
`computationalSpecialHVZK_schnorr_ideal` via `computationalSpecialHVZK_linearProbFamily`. -/
theorem computationalSpecialHVZK_schnorr (setup : ℕ → PMF F.Desc) :
    ComputationalSpecialHVZK F.schnorrProbFamily (fun i α u => α • F.generator i.2 = u)
      F.schnorrEncoding (fun i => F.encScalar i.2) (fun n => (setup n).map (n, ·))
      F.schnorrSimulator (fun _ => 0) :=
  F.computationalSpecialHVZK_linearProbFamily (F.computationalSpecialHVZK_schnorr_ideal setup)

/-! ### Shared bit-encoded Schnorr key generation, commitment, response, and verification -/

/-- Ideal encoded Schnorr key generation for group description `d`: sample a uniform secret scalar
`α : ZMod (F.order d)` and output the encoded public key `F.encode d (α • F.generator d)` paired
with the binary-encoded secret key `F.encScalar d α`. -/
noncomputable def schnorrIdealKeyGen (d : F.Desc) : PMF (List Bool × List Bool) :=
  (PMF.uniformOfFintype (ZMod (F.order d))).map
    fun α => (F.encode d (α • F.generator d), F.encScalar d α)

/-- Bit-encoded Schnorr key generation at security parameter `n` and group description `d`
([BonehShoup2023], Sections 19.1–19.2): sample an approximate uniform exponent
`sk ← F.sampleExp n d` and output the encoded public key
`F.smul (d, sk, F.encode d (F.generator d))` together with the binary secret key
`(sk % F.order d).bits`. -/
noncomputable def schnorrSigKeyGen (n : ℕ) (d : F.Desc) : ProbComp (List Bool × List Bool) := do
  let sk ← F.sampleExp n d
  return (F.smul (d, sk, F.encode d (F.generator d)), (sk % F.order d).bits)

/-- Output distribution of `schnorrSigKeyGen`: the sampled exponent modulo `F.order d` determines
the encoded public key `α • g` and secret scalar `α`. -/
theorem eval_schnorrSigKeyGen (n : ℕ) (d : F.Desc) :
    ProbComp.eval (F.schnorrSigKeyGen n d) =
      ((ProbComp.eval (F.sampleExp n d)).map (Nat.cast : ℕ → ZMod (F.order d))).map
        fun α => (F.encode d (α • F.generator d), F.encScalar d α) := by
  rw [schnorrSigKeyGen, ProbComp.eval_bind, PMF.map_comp]
  simp only [ProbComp.eval_pure, F.smul_encode, encScalar, Function.Embedding.coeFn_mk,
    encNat_apply]
  rw [← PMF.bind_pure_comp]
  congr 1 with s : 1
  simp only [Function.comp_apply, ZMod.val_natCast]

/-- `schnorrSigKeyGen n d` is within statistical distance `1 / 2 ^ n` of the ideal encoded Schnorr
key generator `schnorrIdealKeyGen d`. -/
theorem closeTo_schnorrSigKeyGen (n : ℕ) (d : F.Desc) :
    CloseTo (F.schnorrIdealKeyGen d) (ProbComp.eval (F.schnorrSigKeyGen n d))
      (1 / 2 ^ n : ℝ≥0) := by
  rw [schnorrIdealKeyGen, eval_schnorrSigKeyGen]
  exact (F.closeTo_uniform_sampleExp n d).map _

/-- Replacing `schnorrSigKeyGen n d` with an exact uniform secret key
`α ← PMF.uniformOfFintype (ZMod (F.order d))` changes any Boolean continuation on the encoded
public key and secret scalar `(ofBits sk : ZMod (F.order d))` by at most `1 / 2 ^ n`. -/
theorem advantage_bind_schnorrSigKeyGen_le (n : ℕ) (d : F.Desc)
    (continuation : List Bool → ZMod (F.order d) → Game) :
    Game.advantage
      ((ProbComp.eval (F.schnorrSigKeyGen n d)).bind fun pksk =>
        continuation pksk.1 (ofBits pksk.2 : ZMod (F.order d)))
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        continuation (F.encode d (α • F.generator d)) α) ≤ 1 / 2 ^ n := by
  simp only [schnorrSigKeyGen, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind,
    PMF.pure_bind, F.smul_encode, ofBits_bits, ZMod.natCast_mod]
  exact F.advantage_bind_sampleExp_le n d
    (fun α => continuation (F.encode d (α • F.generator d)) α)

/-- **Schnorr key generation is uniform strict PPT** in the unary security parameter and the group
description. -/
theorem isPPTOn_schnorrSigKeyGen :
    IsPPTOn (encPair encUnary F.encDesc) (encPair encBits encBits)
      (fun input => F.schnorrSigKeyGen input.1 input.2) := by
  let encIn := encPair encUnary F.encDesc
  have hn : ComputableInPolyTime (fun p : ℕ × F.Desc => p.1) encIn encUnary := by fun_prop
  have hd : ComputableInPolyTime (fun p : ℕ × F.Desc => p.2) encIn F.encDesc := by fun_prop
  change IsPPTOn encIn (encPair encBits encBits) fun p =>
    F.sampleExp p.1 p.2 >>= fun sk =>
      pure (F.smul (p.2, sk, F.encode p.2 (F.generator p.2)), (sk % F.order p.2).bits)
  refine (F.isPPTOn_sampleExp hn hd).bind_with ?_
  let encMid := encPair encIn encNat
  have hd' : ComputableInPolyTime (fun p : (ℕ × F.Desc) × ℕ => p.1.2) encMid F.encDesc := by
    fun_prop
  have hsk : ComputableInPolyTime (fun p : (ℕ × F.Desc) × ℕ => p.2) encMid encNat := by
    fun_prop
  have hq := F.computableInPolyTime_order.comp hd'
  have hg := F.computableInPolyTime_generator.comp hd'
  have hpk := F.computableInPolyTime_smul.comp (hd'.prod (hsk.prod hg))
  have hsk_bits : ComputableInPolyTime
      (fun p : (ℕ × F.Desc) × ℕ => (p.2 % F.order p.1.2).bits) encMid encBits :=
    (ComputableInPolyTime.binary_mod' hsk hq).encoding_comp
  exact (hpk.prod hsk_bits).isPPTOn

/-- Bit-level Schnorr commitment: given `(d, r)` where `r` is the binary-encoded commitment
exponent, compute the encoded group element `r • g`. -/
def schnorrCommitBits (input : F.Desc × List Bool) : List Bool :=
  let (d, r) := input
  F.smul (d, ofBits r, F.encode d (F.generator d))

/-- On an encoded scalar `r : ZMod (F.order d)`, `schnorrCommitBits` produces
`F.encode d (r • g)`. -/
@[simp] theorem schnorrCommitBits_encScalar (d : F.Desc) (r : ZMod (F.order d)) :
    F.schnorrCommitBits (d, F.encScalar d r) = F.encode d (r • F.generator d) := by
  simp only [schnorrCommitBits, encScalar, Function.Embedding.coeFn_mk, encNat_apply, ofBits_bits,
    F.smul_encode, ZMod.natCast_zmod_val]

/-- **Bit-level Schnorr commitment is computable in polynomial time**. -/
theorem computableInPolyTime_schnorrCommitBits :
    ComputableInPolyTime F.schnorrCommitBits (encPair F.encDesc encBits) encBits := by
  unfold schnorrCommitBits
  fun_prop

/-- Input `(d, a, b, c)` of the bit-level Schnorr response and commitment-recovery maps: a group
description `d`, then three bit words. The description and the first two words are framed. -/
abbrev encSchnorrBitsInput : F.Desc × List Bool × List Bool × List Bool ↪ List Bool :=
  encPair F.encDesc (encPair encBits (encPair encBits encBits))

/-- Bit-level Schnorr response: given `(d, sk, r, roOut)` where `sk` is the encoded secret key, `r`
is the encoded commitment randomness, and `roOut` is the challenge bit string, compute
`((ofBits r + ofBits roOut * ofBits sk) % F.order d).bits`. -/
def schnorrRespondBits (input : F.Desc × List Bool × List Bool × List Bool) : List Bool :=
  let (d, sk, r, roOut) := input
  ((ofBits r + ofBits roOut * ofBits sk) % F.order d).bits

/-- On encoded scalars `α, r : ZMod (F.order d)`, `schnorrRespondBits` computes the encoded scalar
`r + (ofBits roOut : ZMod (F.order d)) * α`. -/
@[simp] theorem schnorrRespondBits_encScalar (d : F.Desc) (α r : ZMod (F.order d))
    (roOut : List Bool) :
    F.schnorrRespondBits (d, F.encScalar d α, F.encScalar d r, roOut) =
      F.encScalar d (r + (ofBits roOut : ZMod (F.order d)) * α) := by
  simp only [schnorrRespondBits, encScalar, Function.Embedding.coeFn_mk, encNat_apply, ofBits_bits]
  congr 1
  rw [← ZMod.val_natCast (F.order d), Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val,
    ZMod.natCast_zmod_val]

/-- **Bit-level Schnorr response is computable in polynomial time**. -/
theorem computableInPolyTime_schnorrRespondBits :
    ComputableInPolyTime F.schnorrRespondBits F.encSchnorrBitsInput encBits := by
  let encIn := encPair F.encDesc (encPair encBits (encPair encBits encBits))
  have hd : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool => p.1) encIn F.encDesc := by fun_prop
  have hsk : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool => p.2.1) encIn encBits := by fun_prop
  have hr : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool => p.2.2.1) encIn encBits := by fun_prop
  have hro : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool => p.2.2.2) encIn encBits := by fun_prop
  have hq := (F.computableInPolyTime_order.comp hd)
  have hsk_nat := ComputableInPolyTime.bitsToNat.comp hsk
  have hr_nat := ComputableInPolyTime.bitsToNat.comp hr
  have hro_nat := ComputableInPolyTime.bitsToNat.comp hro
  exact (ComputableInPolyTime.binary_mod'
    (.binary_add' hr_nat (.binary_mul' hro_nat hsk_nat)) hq).encoding_comp

/-- Bit-level Schnorr commitment recovery ([BonehShoup2023], Sections 19.1 and 19.2.1): given
`(d, pk, c, z)`, compute the encoded group element `z • g - c • pk`. -/
def schnorrRecoverCommitBits (input : F.Desc × List Bool × List Bool × List Bool) : List Bool :=
  let (d, pk, roOut, z) := input
  F.add (d, F.smul (d, ofBits z, F.encode d (F.generator d)),
    F.smul (d, F.order d - ofBits roOut % F.order d, pk))

/-- **Bit-level Schnorr commitment recovery is computable in polynomial time**. -/
theorem computableInPolyTime_schnorrRecoverCommitBits :
    ComputableInPolyTime F.schnorrRecoverCommitBits F.encSchnorrBitsInput encBits := by
  let encIn := encPair F.encDesc (encPair encBits (encPair encBits encBits))
  have hd : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool => p.1) encIn F.encDesc := by fun_prop
  have hpk : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool => p.2.1) encIn encBits := by fun_prop
  have hro : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool => p.2.2.1) encIn encBits := by fun_prop
  have hz : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool => p.2.2.2) encIn encBits := by fun_prop
  exact F.computableInPolyTime_add_smul_sub_mod hd (ComputableInPolyTime.bitsToNat.comp hz)
    (F.computableInPolyTime_generator.comp hd) hro hpk

/-- On an encoded public key `pk = F.encode d u`, `schnorrRecoverCommitBits` computes the encoding
of `z • g - roOut • u`. -/
@[simp] theorem schnorrRecoverCommitBits_encode (d : F.Desc) (u : F.Carrier d)
    (roOut z : List Bool) :
    F.schnorrRecoverCommitBits (d, F.encode d u, roOut, z) =
      F.encode d ((ofBits z : ZMod (F.order d)) • F.generator d -
        (ofBits roOut : ZMod (F.order d)) • u) := by
  simp only [schnorrRecoverCommitBits, F.smul_encode, F.add_encode, ZMod.natCast_sub_mod_eq_neg,
    neg_smul, ← sub_eq_add_neg]

/-- Polynomial-time Schnorr verification on an encoded public key `pk`, commitment word `t`,
challenge word `c`, and response word `z`: compares `t` with the canonical commitment recovery
`schnorrRecoverCommitBits (d, pk, c, z)`. -/
def encodeSchnorrVerify (d : F.Desc) (pk t c z : List Bool) : Bool :=
  t == F.schnorrRecoverCommitBits (d, pk, c, z)

/-- On a canonical encoded public key `F.encode d u`, `encodeSchnorrVerify` agrees with the
algebraic Schnorr verification check `t = encode (z • g - c • u)`. -/
@[simp]
theorem encodeSchnorrVerify_encode (d : F.Desc) (u : F.Carrier d) (t c z : List Bool) :
    F.encodeSchnorrVerify d (F.encode d u) t c z =
      decide (t = F.encode d ((ofBits z : ZMod (F.order d)) • F.generator d -
        (ofBits c : ZMod (F.order d)) • u)) := by
  simp only [encodeSchnorrVerify, schnorrRecoverCommitBits_encode, beq_eq_decide]

/-- Under a canonical public key `F.encode d u`, `encodeSchnorrVerify` accepts if and only if `t`
equals the canonical encoding of `z • g - c • u`. -/
theorem encodeSchnorrVerify_eq_true_iff (d : F.Desc) (u : F.Carrier d) (t c z : List Bool) :
    F.encodeSchnorrVerify d (F.encode d u) t c z = true ↔
      t = F.encode d ((ofBits z : ZMod (F.order d)) • F.generator d -
        (ofBits c : ZMod (F.order d)) • u) := by
  simp only [encodeSchnorrVerify, schnorrRecoverCommitBits_encode, beq_iff_eq]

/-- `encodeSchnorrVerify` is computable in polynomial time. -/
theorem computableInPolyTime_encodeSchnorrVerify :
    ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool × List Bool =>
        F.encodeSchnorrVerify p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
      (encPair F.encDesc (encPair encBits (encPair encBits (encPair encBits encBits))))
      encBool := by
  let encIn := encPair F.encDesc (encPair encBits (encPair encBits (encPair encBits encBits)))
  have hd : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool × List Bool => p.1)
      encIn F.encDesc := by fun_prop
  have hpk : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool × List Bool => p.2.1)
      encIn encBits := by fun_prop
  have ht : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool × List Bool => p.2.2.1)
      encIn encBits := by fun_prop
  have hc : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool × List Bool => p.2.2.2.1)
      encIn encBits := by fun_prop
  have hz : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool × List Bool => p.2.2.2.2)
      encIn encBits := by fun_prop
  have hrecover := F.computableInPolyTime_schnorrRecoverCommitBits.comp
    (hd.prod (hpk.prod (hc.prod hz)))
  have hbeq : ComputableInPolyTime (fun q : List Bool × List Bool => q.1 == q.2)
      (encPair encBits encBits) encBool := by fun_prop
  exact hbeq.comp (ht.prod hrecover)

/-- Composition rule for `encodeSchnorrVerify`. -/
@[fun_prop]
theorem computableInPolyTime_encodeSchnorrVerify_comp {γ : Type} {encIn : γ ↪ List Bool}
    {d : γ → F.Desc} {pk t c z : γ → List Bool}
    (hd : ComputableInPolyTime d encIn F.encDesc)
    (hpk : ComputableInPolyTime pk encIn encBits)
    (ht : ComputableInPolyTime t encIn encBits)
    (hc : ComputableInPolyTime c encIn encBits)
    (hz : ComputableInPolyTime z encIn encBits) :
    ComputableInPolyTime (fun a => F.encodeSchnorrVerify (d a) (pk a) (t a) (c a) (z a))
      encIn encBool :=
  F.computableInPolyTime_encodeSchnorrVerify.comp (hd.prod (hpk.prod (ht.prod (hc.prod hz))))

/-- The uniform strict PPT program `schnorrSigKeyGen` (`isPPTOn_schnorrSigKeyGen`) computes the
encoded commitment and scalar private state of `schnorrProbCommit` on encodings (the commitment
`r • g` uses neither the witness `α` nor the statement `u`; see [BonehShoup2023], Figure 19.1,
p. 756, and the remark after Example 19.1, p. 773, that the prover does not use the
statement). -/
theorem eval_schnorrSigKeyGen_eq_schnorrProbCommit (i : ℕ × F.Desc) (α : ZMod (F.order i.2))
    (u : F.Carrier i.2) :
    ProbComp.eval (F.schnorrSigKeyGen i.1 i.2) =
      (ProbComp.eval (F.schnorrProbCommit i α u)).map
        (Prod.map (F.schnorrEncoding.commitment i) (F.encScalar i.2)) := by
  simp only [eval_schnorrSigKeyGen, schnorrProbCommit, linearProbCommit, ProbComp.eval_map,
    PMF.map_comp]
  rfl

/-- `schnorrRespondBits` (`computableInPolyTime_schnorrRespondBits`) computes the response step of
`schnorrProbFamily` on encodings. -/
theorem schnorrRespondBits_schnorrProbFamily (i : ℕ × F.Desc) (α : ZMod (F.order i.2))
    (u : F.Carrier i.2) (r c : ZMod (F.order i.2)) :
    F.schnorrRespondBits
        (i.2, F.encScalar i.2 α, F.encScalar i.2 r, F.schnorrEncoding.challenge i c) =
      F.schnorrEncoding.response i ((F.schnorrProbFamily i).respond α u r c) := by
  rw [schnorrRespondBits_encScalar]
  simp only [schnorrEncoding, schnorrProbFamily, linearProbFamily, encScalar,
    Function.Embedding.coeFn_mk, encNat_apply, ofBits_bits, ZMod.natCast_zmod_val,
    Function.Embedding.refl_apply, smul_eq_mul]

/-- `encodeSchnorrVerify` realizes the verifier of `schnorrFamily` on `schnorrEncoding`. -/
theorem verifierRealizedBy_encodeSchnorrVerify :
    VerifierRealizedBy F.schnorrFamily F.schnorrEncoding
      (fun ((_, d), pk, t, c, z) => F.encodeSchnorrVerify d pk t c z) := by
  rintro ⟨n, d⟩ u t c z
  rw [Bool.eq_iff_iff]
  change _ ↔ (F.schnorrFamily (n, d)).Accepts u t c z
  rw [schnorrFamily, schnorr_accepts_iff]
  simp only [schnorrEncoding, encodeEmbedding, encScalar, Function.Embedding.coeFn_mk,
    encNat_apply, encodeSchnorrVerify_encode, ofBits_bits, ZMod.natCast_zmod_val,
    decide_eq_true_eq, (F.encode_injective d).eq_iff, Function.Embedding.refl_apply,
    eq_sub_iff_add_eq]
  exact eq_comm

/-- **Schnorr's Sigma protocol has a deterministic polynomial-time verifier.** -/
theorem efficientVerifier_schnorr :
    EfficientVerifier F.schnorrFamily F.schnorrEncoding :=
  ⟨fun ((_, d), pk, t, c, z) => F.encodeSchnorrVerify d pk t c z, by fun_prop,
    F.verifierRealizedBy_encodeSchnorrVerify⟩

/-- **Schnorr's fair-coin Sigma protocol has a deterministic polynomial-time verifier.** -/
theorem efficientVerifier_schnorrProb :
    EfficientVerifier F.schnorrProbFamily F.schnorrEncoding :=
  F.efficientVerifier_schnorr

end Cslib.Crypto.PrimeOrderGroupFamily
