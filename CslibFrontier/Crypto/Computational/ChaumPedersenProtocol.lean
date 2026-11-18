/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SchnorrProtocol
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Foundations.Data.ZMod.NatCast
import CslibFrontier.Tactic.PPT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip

/-!
# The Chaum–Pedersen protocol with a fair-coin prover, extractor and simulator

The Chaum–Pedersen protocol for Diffie–Hellman triples ([BonehShoup2023], Section 19.5.2,
Figure 19.7 and Theorem 19.10, pp. 777–778) over a `PrimeOrderGroupFamily`, as a family indexed by
a unary security parameter `n` and a group description `d`, with challenges in `ZMod q` for the
group order `q`. A statement is a triple `(u, v, w)` of group elements and a witness is `β` with
`β • g = v` and `β • u = w` ([BonehShoup2023], (19.12), in additive notation). Statements and
commitments are framed tuples of the family's element encoding, and scalars are binary
(`chaumPedersenEncoding`).

`chaumPedersenProbFamily` equips the protocol with the fair-coin commitment sampler
`chaumPedersenCommit`, which draws its commitment nonce with `sampleExp n d` (within statistical
distance `1 / 2 ^ n` of uniform on `ZMod q`). Both prover rounds have uniform polynomial-time word
realizations (`chaumPedersenCommitWord` and `schnorrRespondBits`), and `chaumPedersenFamily` keeps
the exact-uniform `ZMod q` commitment law (`SigmaProtocol.linear`) used as the ideal-sampling
intermediate step:

* **Completeness and certified prover** (`chaumPedersenProbFamily_complete`,
  `eval_chaumPedersenCommitWord`, `isPPTOn_chaumPedersenCommitWord`,
  `schnorrRespondBits_chaumPedersen`, Theorem 19.10 with Definition 19.3): honest conversations of
  `chaumPedersenProbFamily` always accept, and its commitment and response rounds are uniform strict
  PPT and deterministic polynomial time on encodings (`efficientVerifier_chaumPedersenProb` in
  `CslibFrontier.Crypto.Computational.ChaumPedersenProtocol.Verifier` certifies the verifier).
* **Efficient special soundness** (`efficientSpecialSoundness_chaumPedersenProb` and
  `efficientSpecialSoundness_chaumPedersen`, Theorem 19.10 with Definition 19.4): the extractor
  `chaumPedersenExtract` computes `(c - c')⁻¹ (z - z')` with `extractNat`. It reads neither the
  statement nor the commitment, so its polynomial-time word function is Schnorr's
  `schnorrExtractWord`.
* **Statistical closeness and computational special HVZK for the fair-coin prover**
  (`closeTo_transcript_chaumPedersenProbFamily`,
  `closeTo_transcript_chaumPedersenProbFamily_simulator`,
  `advantage_chvzkRealGame_chaumPedersenProbFamily_le`,
  `advantage_chvzkGame_chaumPedersenProbFamily_le`,
  `computationalSpecialHVZK_chaumPedersen`, Theorem 19.10 with Definitions 19.5 and 20.6):
  Theorem 19.10 states exact special HVZK (Definition 19.5(ii), identical transcript distribution,
  which relies on Definition 2.8, p. 30, permitting negligible runtime-overflow probability and
  exact rejection sampling on `ZMod q`); in the strict-PPT fair-coin model exact simulation is
  impossible when `q` is not a power of two, so this module establishes the `2 / 2 ^ n` statistical
  form (`closeTo_transcript_chaumPedersenProbFamily_simulator`) and Definition 20.6
  (`computationalSpecialHVZK_chaumPedersen`). Boneh and Shoup's simulator samples a uniform response
  `z` and outputs `((z • g - c • v, z • u - c • w), z)`. The typed simulator
  `chaumPedersenSimulator` (certified strict PPT by `chaumPedersenSimulateWord`) samples `z` with
  `sampleExp`, incurring `1 / 2 ^ n` against the ideal-nonce prover
  (`efficientSpecialHVZK_chaumPedersen_ideal`) and `2 / 2 ^ n` against the fair-coin prover
  `chaumPedersenProbFamily` at every challenge on valid triples, with Attack Game 20.4 advantage at
  most `2 / 2 ^ n` against arbitrary adversaries and exact zero acceptance error
  (`accepts_chaumPedersenSimulator`, `δ = fun _ => 0`) along any group-description setup.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.chaumPedersenCommit`,
  `Cslib.Crypto.PrimeOrderGroupFamily.chaumPedersenCommitWord`,
  `Cslib.Crypto.PrimeOrderGroupFamily.chaumPedersenProbFamily`: the fair-coin commitment sampler,
  its strict-PPT word program, and the fair-coin Chaum–Pedersen Sigma protocol family.
* `Cslib.Crypto.PrimeOrderGroupFamily.chaumPedersenFamily`: the ideal-nonce protocol at each index.
* `Cslib.Crypto.PrimeOrderGroupFamily.chaumPedersenEncoding`: its word encodings.
* `Cslib.Crypto.PrimeOrderGroupFamily.chaumPedersenExtract`: the extractor.
* `Cslib.Crypto.PrimeOrderGroupFamily.chaumPedersenSimulator`,
  `Cslib.Crypto.PrimeOrderGroupFamily.chaumPedersenSimulateWord`: the simulator with `sampleExp`
  and the strict PPT word program computing it.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.chaumPedersenProbFamily_complete`,
  `Cslib.Crypto.PrimeOrderGroupFamily.eval_chaumPedersenCommitWord`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_chaumPedersenCommitWord`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrRespondBits_chaumPedersen`
* `Cslib.Crypto.PrimeOrderGroupFamily.efficientSpecialSoundness_chaumPedersenProb`,
  `Cslib.Crypto.PrimeOrderGroupFamily.efficientSpecialSoundness_chaumPedersen`
* `Cslib.Crypto.PrimeOrderGroupFamily.closeTo_transcript_chaumPedersenProbFamily`,
  `Cslib.Crypto.PrimeOrderGroupFamily.closeTo_transcript_chaumPedersenProbFamily_simulator`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_chvzkRealGame_chaumPedersenProbFamily_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_chvzkGame_chaumPedersenProbFamily_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computationalSpecialHVZK_chaumPedersen`

## Ideal-sampling steps

* `Cslib.Crypto.PrimeOrderGroupFamily.efficientSpecialHVZK_chaumPedersen_ideal`: statistical
  special HVZK against the ideal-nonce prover `chaumPedersenFamily`, consumed by
  `closeTo_transcript_chaumPedersenProbFamily_simulator` and
  `advantage_chvzkGame_chaumPedersenProbFamily_le`.
* `Cslib.Crypto.PrimeOrderGroupFamily.computationalSpecialHVZK_chaumPedersen_ideal`: computational
  special HVZK against the ideal-nonce prover `chaumPedersenFamily`, consumed by
  `computationalSpecialHVZK_chaumPedersen`.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 19.4 (Definitions 19.3–19.5, pp. 772–774), Section 19.5.2
  (Figure 19.7 and Theorem 19.10, pp. 777–778), and Section 20.4.2 (Attack Game 20.4 and
  Definition 20.6, p. 840).
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Protocols Protocols.SigmaProtocol Interactive
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)

/-- The Chaum–Pedersen protocol ([BonehShoup2023], Section 19.5.2) in the group described by
`i.2`, with challenges in `ZMod q`. The security parameter `i.1` does not change the protocol. The
honest prover draws its commitment nonce exactly uniformly on `ZMod q` at the `PMF` level, an
ideal sampler that no fair-coin machine with a strict polynomial time bound realizes exactly when
`q` is not a power of two; `chaumPedersenProbFamily` equips the protocol with the fair-coin
commitment sampler `chaumPedersenCommit`. -/
@[expose] noncomputable def chaumPedersenFamily (i : ℕ × F.Desc) :
    SigmaProtocol (ZMod (F.order i.2)) (F.Carrier i.2 × F.Carrier i.2 × F.Carrier i.2)
      (F.Carrier i.2 × F.Carrier i.2) (ZMod (F.order i.2)) (ZMod (F.order i.2)) :=
  chaumPedersen (Function.Embedding.refl _) (F.generator i.2)

/-- The fair-coin commitment sampler of the Chaum–Pedersen prover ([BonehShoup2023],
Section 19.5.2, Figure 19.7, p. 777): at index `(n, d)` and statement `(u, v, w)`, sample `s` with
`sampleExp n d`, read it as `r = (s : ZMod q)`, and return the commitment `(r • g, r • u)` together
with the prover state `r`. -/
@[expose] noncomputable def chaumPedersenCommit (i : ℕ × F.Desc) (_ : ZMod (F.order i.2))
    (y : F.Carrier i.2 × F.Carrier i.2 × F.Carrier i.2) :
    ProbComp ((F.Carrier i.2 × F.Carrier i.2) × ZMod (F.order i.2)) :=
  (fun r : ZMod (F.order i.2) => ((r • F.generator i.2, r • y.1), r)) <$>
    ((Nat.cast : ℕ → ZMod (F.order i.2)) <$> F.sampleExp i.1 i.2)

/-- The Chaum–Pedersen commitment sampler on words: on the index `(n, d)` and an encoded statement
`(u, v, w)`, sample `s` with `sampleExp n d` and return the encoded commitment `(s • g, s • u)` and
the binary state `(s % q).bits`. It certifies `chaumPedersenCommit` (`eval_chaumPedersenCommitWord`,
`isPPTOn_chaumPedersenCommitWord`). -/
noncomputable def chaumPedersenCommitWord :
    (ℕ × F.Desc) × List Bool → ProbComp (List Bool × List Bool)
  | ((n, d), y) => do
    let s ← F.sampleExp n d
    return (encPair encBits encBits
        (F.smul (d, s, F.encode d (F.generator d)),
          F.smul (d, s, unframe y)),
      (s % F.order d).bits)

/-- The Chaum–Pedersen Sigma protocol ([BonehShoup2023], Section 19.5.2, Figure 19.7, p. 777) with
a fair-coin prover: at index `(n, d)`, the honest prover commits with `chaumPedersenCommit` (using
`sampleExp n d`), answers a challenge `c` with `r + c * β`, and the verifier checks
`z • g = t₁ + c • v` and `z • u = t₂ + c • w`. -/
@[expose] noncomputable def chaumPedersenProbFamily (i : ℕ × F.Desc) :
    SigmaProtocol (ZMod (F.order i.2)) (F.Carrier i.2 × F.Carrier i.2 × F.Carrier i.2)
      (F.Carrier i.2 × F.Carrier i.2) (ZMod (F.order i.2)) (ZMod (F.order i.2)) where
  State := ZMod (F.order i.2)
  commit x y := ProbComp.eval (F.chaumPedersenCommit i x y)
  respond := (F.chaumPedersenFamily i).respond
  verify := (F.chaumPedersenFamily i).verify

/-- The word encodings of `chaumPedersenFamily`: the unary security parameter with the
description, statements `(u, v, w)` and commitments `(t₁, t₂)` as framed tuples of the family's
element encoding, and challenges and responses in binary. -/
@[expose] def chaumPedersenEncoding :
    Encoding (ℕ × F.Desc) (fun i => F.Carrier i.2 × F.Carrier i.2 × F.Carrier i.2)
      (fun i => F.Carrier i.2 × F.Carrier i.2) (fun i => ZMod (F.order i.2))
      (fun i => ZMod (F.order i.2)) where
  index := encPair encUnary F.encDesc
  statement i :=
    encPair (F.encodeEmbedding i.2) (encPair (F.encodeEmbedding i.2) (F.encodeEmbedding i.2))
  commitment i := encPair (F.encodeEmbedding i.2) (F.encodeEmbedding i.2)
  challenge i := F.encScalar i.2
  response i := F.encScalar i.2

/-- The Chaum–Pedersen extractor ([BonehShoup2023], Theorem 19.10), computed with `extractNat`: it
is `(c - c')⁻¹ (z - z')` whenever `c ≠ c'`, and reads neither the statement nor the commitment. -/
@[expose] def chaumPedersenExtract (i : ℕ × F.Desc)
    (_ : F.Carrier i.2 × F.Carrier i.2 × F.Carrier i.2)
    (_ : F.Carrier i.2 × F.Carrier i.2) (c z c' z' : ZMod (F.order i.2)) : ZMod (F.order i.2) :=
  extractNat (F.order i.2) c.val z.val c'.val z'.val

/-- The Chaum–Pedersen simulator ([BonehShoup2023], Theorem 19.10) with fair coins: at index
`(n, d)`, on a statement `(u, v, w)` and a challenge `c`, sample `s` with `sampleExp n d`, read it
as the response `z = s mod q`, and return the commitment `(z • g - c • v, z • u - c • w)` with
`z`. -/
noncomputable def chaumPedersenSimulator :
    Simulator (ℕ × F.Desc) (fun i => F.Carrier i.2 × F.Carrier i.2 × F.Carrier i.2)
      (fun i => F.Carrier i.2 × F.Carrier i.2) (fun i => ZMod (F.order i.2))
      (fun i => ZMod (F.order i.2)) :=
  fun i (u, v, w) c =>
    (fun z => ((z • F.generator i.2 - c • v, z • u - c • w), z)) <$>
      ((Nat.cast : ℕ → ZMod (F.order i.2)) <$> F.sampleExp i.1 i.2)

/-- The Chaum–Pedersen simulator on words: on the index `(n, d)`, an encoded statement
`(u, v, w)` and a binary challenge `c`, sample `s` with `sampleExp n d` and return the encoding of
`(s • g - c • v, s • u - c • w)` and of `s mod q`. It is the strict PPT certificate of
`chaumPedersenSimulator` (`eval_chaumPedersenSimulateWord`). -/
noncomputable def chaumPedersenSimulateWord :
    (ℕ × F.Desc) × List Bool × List Bool → ProbComp (List Bool × List Bool)
  | ((n, d), y, c) => do
    let s ← F.sampleExp n d
    return (encPair encBits encBits
        (F.add (d, F.smul (d, s, F.encode d (F.generator d)),
          F.smul (d, F.order d - ofBits c % F.order d, unframe (dropFrame y))),
        F.add (d, F.smul (d, s, unframe y),
          F.smul (d, F.order d - ofBits c % F.order d, dropFrame (dropFrame y)))),
      (s % F.order d).bits)

/-! ### Special soundness -/

/-- Schnorr's `schnorrExtractWord` computes the Chaum–Pedersen extractor on encodings. -/
private theorem extractorRealizedBy_chaumPedersen :
    ExtractorRealizedBy F.chaumPedersenEncoding (fun i => F.encScalar i.2) F.chaumPedersenExtract
      F.schnorrExtractWord := by
  intro i y t c z c' z'
  simp only [schnorrExtractWord, chaumPedersenEncoding, encScalar,
    Function.Embedding.coeFn_mk, encNat_apply, ofBits_bits, chaumPedersenExtract,
    ZMod.val_natCast, extractNat, Nat.mod_mod]

/-- **The Chaum–Pedersen protocol has efficient special soundness** ([BonehShoup2023],
Theorem 19.10 with Definition 19.4). -/
theorem efficientSpecialSoundness_chaumPedersen :
    EfficientSpecialSoundness F.chaumPedersenFamily
      (fun i β (u, v, w) => β • F.generator i.2 = v ∧ β • u = w)
      F.chaumPedersenEncoding (fun i => F.encScalar i.2) F.chaumPedersenExtract where
  specialSoundness i y t c z c' z' hc hz hz' := by
    have h := chaumPedersen_specialSoundness (ι := Function.Embedding.refl _)
      (g := F.generator i.2) y t c z c' z' hc hz hz'
    simp only [linearExtract, Function.Embedding.refl_apply, smul_eq_mul] at h
    simpa only [chaumPedersenExtract, extractNat_zmod_val hc] using h
  polyTime := ⟨F.schnorrExtractWord, F.computableInPolyTime_schnorrExtractWord,
    F.extractorRealizedBy_chaumPedersen⟩

/-- **The fair-coin Chaum–Pedersen protocol has efficient special soundness** ([BonehShoup2023],
Theorem 19.10 with Definition 19.4). -/
theorem efficientSpecialSoundness_chaumPedersenProb :
    EfficientSpecialSoundness F.chaumPedersenProbFamily
      (fun i β (u, v, w) => β • F.generator i.2 = v ∧ β • u = w)
      F.chaumPedersenEncoding (fun i => F.encScalar i.2) F.chaumPedersenExtract where
  specialSoundness := F.efficientSpecialSoundness_chaumPedersen.specialSoundness
  polyTime := F.efficientSpecialSoundness_chaumPedersen.polyTime

/-! ### Fair-coin prover completeness and efficiency -/

/-- **Completeness of the fair-coin Chaum–Pedersen protocol** ([BonehShoup2023], Theorem 19.10
with Definition 19.3): for every valid witness-statement pair `(β, (u, v, w))` and challenge `c`,
every honest transcript of `chaumPedersenProbFamily` is accepting. -/
theorem chaumPedersenProbFamily_complete (i : ℕ × F.Desc) :
    (F.chaumPedersenProbFamily i).Complete
      fun β (u, v, w) => β • F.generator i.2 = v ∧ β • u = w := by
  rintro β ⟨u, v, w⟩ ⟨hv, hw⟩ c tz htz
  simp only [SigmaProtocol.transcript, chaumPedersenProbFamily, chaumPedersenCommit,
    ProbComp.eval_map, PMF.map_comp, PMF.mem_support_map_iff] at htz
  obtain ⟨s, -, rfl⟩ := htz
  change (chaumPedersen (Function.Embedding.refl _) (F.generator i.2)).Accepts (u, v, w)
    ((s : ZMod (F.order i.2)) • F.generator i.2, (s : ZMod (F.order i.2)) • u) c
    ((s : ZMod (F.order i.2)) + c * β)
  rw [chaumPedersen_accepts_iff]
  simp only [Function.Embedding.refl_apply, add_smul, mul_smul, hv, hw, and_self]

/-- On an encoded statement, `chaumPedersenCommitWord` computes the encoded commitment and scalar
state of `chaumPedersenCommit`. -/
theorem eval_chaumPedersenCommitWord (i : ℕ × F.Desc) (β : ZMod (F.order i.2))
    (y : F.Carrier i.2 × F.Carrier i.2 × F.Carrier i.2) :
    ProbComp.eval (F.chaumPedersenCommitWord (i, F.chaumPedersenEncoding.statement i y)) =
      (ProbComp.eval (F.chaumPedersenCommit i β y)).map
        (Prod.map (F.chaumPedersenEncoding.commitment i) (F.encScalar i.2)) := by
  obtain ⟨n, d⟩ := i
  obtain ⟨u, v, w⟩ := y
  rw [show (F.chaumPedersenEncoding.statement (n, d)) (u, v, w) =
      encPair (F.encodeEmbedding d) (encPair (F.encodeEmbedding d) (F.encodeEmbedding d))
        (u, v, w) from rfl,
    chaumPedersenCommitWord, ProbComp.eval_bind, chaumPedersenCommit, ProbComp.eval_map,
    ProbComp.eval_map, PMF.map_comp, PMF.map_comp]
  simp only [ProbComp.eval_pure, unframe_encPair, encodeEmbedding, Function.Embedding.coeFn_mk,
    F.smul_encode]
  rw [← PMF.bind_pure_comp]
  congr 1 with s : 1
  simp only [Function.comp_apply, Prod.map, chaumPedersenEncoding, encodeEmbedding, encScalar,
    Function.Embedding.coeFn_mk, encNat_apply, ZMod.val_natCast, encPair_apply, encBits,
    Function.Embedding.refl_apply]

/-- `chaumPedersenCommitWord` is uniform strict PPT in the security parameter, the group
description and the encoded statement. -/
theorem isPPTOn_chaumPedersenCommitWord :
    IsPPTOn (encPair F.chaumPedersenEncoding.index encBits) (encPair encBits encBits)
      F.chaumPedersenCommitWord := by
  let encIn := encPair (encPair encUnary F.encDesc) encBits
  have hn : ComputableInPolyTime (fun p : (ℕ × F.Desc) × List Bool => p.1.1)
      encIn encUnary := by fun_prop
  have hd : ComputableInPolyTime (fun p : (ℕ × F.Desc) × List Bool => p.1.2)
      encIn F.encDesc := by fun_prop
  change IsPPTOn encIn _ fun p => F.sampleExp p.1.1 p.1.2 >>= fun s =>
    pure (encPair encBits encBits
        (F.smul (p.1.2, s, F.encode p.1.2 (F.generator p.1.2)),
          F.smul (p.1.2, s, unframe p.2)),
      (s % F.order p.1.2).bits)
  refine (F.isPPTOn_sampleExp hn hd).bind_with ?_
  let encMid := encPair encIn encNat
  have hd' : ComputableInPolyTime (fun p : ((ℕ × F.Desc) × List Bool) × ℕ => p.1.1.2)
      encMid F.encDesc := by fun_prop
  have hs : ComputableInPolyTime (fun p : ((ℕ × F.Desc) × List Bool) × ℕ => p.2)
      encMid encNat := by fun_prop
  have hy : ComputableInPolyTime (fun p : ((ℕ × F.Desc) × List Bool) × ℕ => p.1.2)
      encMid encBits := by fun_prop
  have hu := ComputableInPolyTime.unframe.comp hy
  have hq := F.computableInPolyTime_order.comp hd'
  have ht₁ := F.computableInPolyTime_smul.comp
    (hd'.prod (hs.prod (F.computableInPolyTime_generator.comp hd')))
  have ht₂ := F.computableInPolyTime_smul.comp (hd'.prod (hs.prod hu))
  have hz : ComputableInPolyTime
      (fun p : ((ℕ × F.Desc) × List Bool) × ℕ => (p.2 % F.order p.1.1.2).bits)
      encMid encBits :=
    (ComputableInPolyTime.binary_mod' hs hq).encoding_comp
  exact ((ht₁.prod ht₂).encoding_comp.prod hz).isPPTOn

/-- `schnorrRespondBits` (`computableInPolyTime_schnorrRespondBits`) computes the response step of
`chaumPedersenProbFamily` on encodings. -/
theorem schnorrRespondBits_chaumPedersen (i : ℕ × F.Desc) (β : ZMod (F.order i.2))
    (y : F.Carrier i.2 × F.Carrier i.2 × F.Carrier i.2) (r c : ZMod (F.order i.2)) :
    F.schnorrRespondBits
        (i.2, F.encScalar i.2 β, F.encScalar i.2 r, F.chaumPedersenEncoding.challenge i c) =
      F.chaumPedersenEncoding.response i ((F.chaumPedersenProbFamily i).respond β y r c) := by
  rw [schnorrRespondBits_encScalar]
  simp only [chaumPedersenEncoding, chaumPedersenProbFamily, chaumPedersenFamily, chaumPedersen,
    linear, encScalar, Function.Embedding.coeFn_mk, encNat_apply, ofBits_bits,
    ZMod.natCast_zmod_val, Function.Embedding.refl_apply, smul_eq_mul]

/-! ### Special HVZK -/

/-- On an encoded statement and challenge, `chaumPedersenSimulateWord` computes the encoded output
of `chaumPedersenSimulator`. -/
theorem eval_chaumPedersenSimulateWord (i : ℕ × F.Desc)
    (y : F.Carrier i.2 × F.Carrier i.2 × F.Carrier i.2) (c : ZMod (F.order i.2)) :
    ProbComp.eval (F.chaumPedersenSimulateWord
        (i, F.chaumPedersenEncoding.statement i y, F.chaumPedersenEncoding.challenge i c)) =
      (ProbComp.eval (F.chaumPedersenSimulator i y c)).map
        (Prod.map (F.chaumPedersenEncoding.commitment i) (F.chaumPedersenEncoding.response i)) := by
  obtain ⟨n, d⟩ := i
  obtain ⟨u, v, w⟩ := y
  have hneg : ((F.order d - c.val % F.order d : ℕ) : ZMod (F.order d)) = -c := by
    rw [ZMod.natCast_sub_mod_eq_neg, ZMod.natCast_zmod_val]
  rw [show (F.chaumPedersenEncoding.statement (n, d)) (u, v, w) =
      encPair (F.encodeEmbedding d) (encPair (F.encodeEmbedding d) (F.encodeEmbedding d))
        (u, v, w) from rfl,
    show (F.chaumPedersenEncoding.challenge (n, d)) c = encNat c.val from rfl,
    chaumPedersenSimulateWord, ProbComp.eval_bind, chaumPedersenSimulator, ProbComp.eval_map,
    ProbComp.eval_map, PMF.map_comp, PMF.map_comp]
  simp only [ProbComp.eval_pure, encNat_apply, ofBits_bits, unframe_encPair, dropFrame_encPair,
    encodeEmbedding, Function.Embedding.coeFn_mk, F.smul_encode, F.add_encode, hneg, neg_smul,
    ← sub_eq_add_neg]
  rw [← PMF.bind_pure_comp]
  congr 1 with a : 1
  simp only [Function.comp_apply, Prod.map, chaumPedersenEncoding, encodeEmbedding, encScalar,
    Function.Embedding.coeFn_mk, encNat_apply, ZMod.val_natCast, encPair_apply, encBits,
    Function.Embedding.refl_apply]

/-- `chaumPedersenSimulateWord` is uniform strict PPT in the security parameter, the description
and the encoded statement and challenge. -/
theorem isPPTOn_chaumPedersenSimulateWord :
    IsPPTOn (encPair (encPair encUnary F.encDesc) (encPair encBits encBits))
      (encPair encBits encBits) F.chaumPedersenSimulateWord := by
  let encIn := encPair (encPair encUnary F.encDesc) (encPair encBits encBits)
  have hn : ComputableInPolyTime (fun p : (ℕ × F.Desc) × List Bool × List Bool => p.1.1)
      encIn encUnary := by fun_prop
  have hd : ComputableInPolyTime (fun p : (ℕ × F.Desc) × List Bool × List Bool => p.1.2)
      encIn F.encDesc := by fun_prop
  change IsPPTOn encIn _ fun p => F.sampleExp p.1.1 p.1.2 >>= fun s =>
    pure (encPair encBits encBits
        (F.add (p.1.2, F.smul (p.1.2, s, F.encode p.1.2 (F.generator p.1.2)),
          F.smul (p.1.2, F.order p.1.2 - ofBits p.2.2 % F.order p.1.2,
            unframe (dropFrame p.2.1))),
        F.add (p.1.2, F.smul (p.1.2, s, unframe p.2.1),
          F.smul (p.1.2, F.order p.1.2 - ofBits p.2.2 % F.order p.1.2,
            dropFrame (dropFrame p.2.1)))),
      (s % F.order p.1.2).bits)
  refine (F.isPPTOn_sampleExp hn hd).bind_with ?_
  let encMid := encPair encIn encNat
  have hd' : ComputableInPolyTime (fun p : ((ℕ × F.Desc) × List Bool × List Bool) × ℕ =>
      p.1.1.2) encMid F.encDesc := by fun_prop
  have hs : ComputableInPolyTime (fun p : ((ℕ × F.Desc) × List Bool × List Bool) × ℕ =>
      p.2) encMid encNat := by fun_prop
  have hy : ComputableInPolyTime (fun p : ((ℕ × F.Desc) × List Bool × List Bool) × ℕ =>
      p.1.2.1) encMid encBits := by fun_prop
  have hc : ComputableInPolyTime (fun p : ((ℕ × F.Desc) × List Bool × List Bool) × ℕ =>
      p.1.2.2) encMid encBits := by fun_prop
  have hu := ComputableInPolyTime.unframe.comp hy
  have hvw := ComputableInPolyTime.dropFrame.comp hy
  have hv := ComputableInPolyTime.unframe.comp hvw
  have hw := ComputableInPolyTime.dropFrame.comp hvw
  have hq := F.computableInPolyTime_order.comp hd'
  have ht₁ := F.computableInPolyTime_add_smul_sub_mod hd' hs
    (F.computableInPolyTime_generator.comp hd') hc hv
  have ht₂ := F.computableInPolyTime_add_smul_sub_mod hd' hs hu hc hw
  have hz : ComputableInPolyTime
      (fun p : ((ℕ × F.Desc) × List Bool × List Bool) × ℕ =>
        (p.2 % F.order p.1.1.2).bits) encMid encBits :=
    (ComputableInPolyTime.binary_mod' hs hq).encoding_comp
  exact ((ht₁.prod ht₂).encoding_comp.prod hz).isPPTOn

/-- `chaumPedersenSimulator` is uniform strict PPT, certified by `chaumPedersenSimulateWord`. -/
theorem isPPT_chaumPedersenSimulator :
    Simulator.IsPPT F.chaumPedersenEncoding F.chaumPedersenSimulator :=
  .of_word F.isPPTOn_chaumPedersenSimulateWord
    fun i y c => (F.eval_chaumPedersenSimulateWord i y c).symm

/-- `chaumPedersenSimulator` realizes the perfect Chaum–Pedersen simulator `linearSimulate`
([BonehShoup2023], Theorem 19.10) up to statistical distance `1 / 2 ^ n` at security parameter
`n`. -/
theorem simulatorRealizedBy_chaumPedersenSimulator :
    SimulatorRealizedBy
      (fun i : ℕ × F.Desc => linearSimulate
        (fun s : F.Carrier i.2 × F.Carrier i.2 × F.Carrier i.2 =>
          (LinearMap.toSpanSingleton (ZMod (F.order i.2)) (F.Carrier i.2) (F.generator i.2)).prod
            (LinearMap.toSpanSingleton (ZMod (F.order i.2)) (F.Carrier i.2) s.1))
        Prod.snd (Function.Embedding.refl _))
      F.chaumPedersenSimulator (fun i => 1 / 2 ^ i.1) :=
  fun i ⟨_, _, _⟩ _ => F.closeTo_map_uniform_sampleExp i.1 i.2 _

/-- Ideal-sampling step toward [BonehShoup2023], Theorem 19.10 (special HVZK, Definition 19.5),
not the cited result: against the honest prover of `chaumPedersenFamily`, which draws its
commitment nonce exactly uniformly on `ZMod q` at the `PMF` level, `linearSimulate` is a perfect
simulator, and the strict PPT simulator `chaumPedersenSimulator` realizes it with statistical
error `1 / 2 ^ n` at security parameter `n`. Consumed by
`closeTo_transcript_chaumPedersenProbFamily_simulator` and
`advantage_chvzkGame_chaumPedersenProbFamily_le` for the fair-coin prover
`chaumPedersenProbFamily`. -/
theorem efficientSpecialHVZK_chaumPedersen_ideal :
    EfficientSpecialHVZK F.chaumPedersenFamily
      (fun i β (u, v, w) => β • F.generator i.2 = v ∧ β • u = w) F.chaumPedersenEncoding
      (fun i => linearSimulate
        (fun s : F.Carrier i.2 × F.Carrier i.2 × F.Carrier i.2 =>
          (LinearMap.toSpanSingleton (ZMod (F.order i.2)) (F.Carrier i.2) (F.generator i.2)).prod
            (LinearMap.toSpanSingleton (ZMod (F.order i.2)) (F.Carrier i.2) s.1))
        Prod.snd (Function.Embedding.refl _))
      (fun i => 1 / 2 ^ i.1) where
  specialHVZK _ := chaumPedersen_specialHVZK
  realized := ⟨_, F.isPPT_chaumPedersenSimulator, F.simulatorRealizedBy_chaumPedersenSimulator⟩

/-- Every output of `chaumPedersenSimulator` is an accepting conversation (acceptance error `0`):
for every sampled `z`, `(z • g - c • v) + c • v = z • g` and `(z • u - c • w) + c • w = z • u`. -/
theorem accepts_chaumPedersenSimulator (i : ℕ × F.Desc)
    (y : F.Carrier i.2 × F.Carrier i.2 × F.Carrier i.2) (c : ZMod (F.order i.2)) :
    (ProbComp.eval (F.chaumPedersenSimulator i y c)).toOuterMeasure
      {tz | (F.chaumPedersenFamily i).Accepts y tz.1 c tz.2} = 1 := by
  obtain ⟨u, v, w⟩ := y
  simp only [chaumPedersenSimulator, ProbComp.eval_map, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_apply_eq_one_iff]
  intro z _
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, chaumPedersenFamily, chaumPedersen_accepts_iff,
    Function.Embedding.refl_apply, sub_add_cancel, and_self]

/-- Ideal-sampling step toward [BonehShoup2023], Theorem 19.10 with Definition 20.6 (special
computational HVZK), not the cited result: Experiment 0 of Attack Game 20.4 runs the honest prover
of `chaumPedersenFamily`, which draws its commitment nonce exactly uniformly on `ZMod q` at the
`PMF` level, and against it the strict PPT simulator `chaumPedersenSimulator` satisfies
Definition 20.6 with zero acceptance error (`δ = fun _ => 0`) over any group-description setup
`setup : ℕ → PMF F.Desc` paired with the security parameter. Consumed by
`computationalSpecialHVZK_chaumPedersen` for the fair-coin prover `chaumPedersenProbFamily`. -/
theorem computationalSpecialHVZK_chaumPedersen_ideal (setup : ℕ → PMF F.Desc) :
    ComputationalSpecialHVZK F.chaumPedersenFamily
      (fun i β (u, v, w) => β • F.generator i.2 = v ∧ β • u = w)
      F.chaumPedersenEncoding (fun i => F.encScalar i.2) (fun n => (setup n).map (n, ·))
      F.chaumPedersenSimulator (fun _ => 0) :=
  F.simulatorRealizedBy_chaumPedersenSimulator.computationalSpecialHVZK_of_accepts
    (fun _ => chaumPedersen_specialHVZK) F.isPPT_chaumPedersenSimulator
    (fun i y c => by rw [F.accepts_chaumPedersenSimulator i y c, tsub_zero])
    (exists_negligible_inv_two_pow_map setup)

/-- At every index `i = (n, d)`, witness `β`, statement `y` and challenge `c`, the honest
transcript of the ideal-nonce `chaumPedersenFamily` and the fair-coin `chaumPedersenProbFamily`
are within statistical distance `1 / 2 ^ n`. -/
theorem closeTo_transcript_chaumPedersenProbFamily (i : ℕ × F.Desc)
    (β : ZMod (F.order i.2)) (y : F.Carrier i.2 × F.Carrier i.2 × F.Carrier i.2)
    (c : ZMod (F.order i.2)) :
    CloseTo ((F.chaumPedersenFamily i).transcript β y c)
      ((F.chaumPedersenProbFamily i).transcript β y c) (1 / 2 ^ i.1) := by
  have hlhs : (F.chaumPedersenFamily i).transcript β y c =
      (PMF.uniformOfFintype (ZMod (F.order i.2))).map
        fun r : ZMod (F.order i.2) =>
          ((r • F.generator i.2, r • y.1), r + c * β) := by
    simp only [chaumPedersenFamily, chaumPedersen, linear_transcript, LinearMap.prod_apply,
      Function.Embedding.refl_apply, smul_eq_mul]
    rfl
  have hrhs : (F.chaumPedersenProbFamily i).transcript β y c =
      ProbComp.eval ((fun r : ZMod (F.order i.2) =>
          ((r • F.generator i.2, r • y.1), r + c * β)) <$>
        ((Nat.cast : ℕ → ZMod (F.order i.2)) <$> F.sampleExp i.1 i.2)) := by
    simp only [SigmaProtocol.transcript, chaumPedersenProbFamily, chaumPedersenCommit,
      chaumPedersenFamily, chaumPedersen, linear, Function.Embedding.refl_apply, smul_eq_mul,
      ProbComp.eval_map, PMF.map_comp, Function.comp_def]
  rw [hlhs, hrhs]
  exact F.closeTo_map_uniform_sampleExp i.1 i.2 _

/-- On every valid witness-statement pair `(β, (u, v, w))` and challenge `c`, the honest transcript
of the fair-coin `chaumPedersenProbFamily` and the output of the strict PPT simulator
`chaumPedersenSimulator` are within statistical distance `2 / 2 ^ n` (`1 / 2 ^ n` from the
prover's `sampleExp` commitment nonce and `1 / 2 ^ n` from the simulator's `sampleExp` response;
[BonehShoup2023], Theorem 19.10 with Definition 19.5, in the strict-PPT fair-coin model). Derived
from `efficientSpecialHVZK_chaumPedersen_ideal` and
`closeTo_transcript_chaumPedersenProbFamily`. -/
theorem closeTo_transcript_chaumPedersenProbFamily_simulator (i : ℕ × F.Desc)
    {β : ZMod (F.order i.2)} {u v w : F.Carrier i.2}
    (hxy : β • F.generator i.2 = v ∧ β • u = w) (c : ZMod (F.order i.2)) :
    CloseTo ((F.chaumPedersenProbFamily i).transcript β (u, v, w) c)
      (ProbComp.eval (F.chaumPedersenSimulator i (u, v, w) c)) (2 / 2 ^ i.1) := by
  have h1 := (F.closeTo_transcript_chaumPedersenProbFamily i β (u, v, w) c).symm
  have h2 := F.simulatorRealizedBy_chaumPedersenSimulator.closeTo_transcript
    F.efficientSpecialHVZK_chaumPedersen_ideal.specialHVZK
    (i := i) (x := β) (y := (u, v, w)) hxy c
  have h12 := h1.trans h2
  have hadd : (1 / 2 ^ i.1 : ℝ≥0∞) + 1 / 2 ^ i.1 = 2 / 2 ^ i.1 := by
    rw [← ENNReal.add_div, one_add_one_eq_two]
  rwa [hadd] at h12

/-- Replacing the ideal-nonce `chaumPedersenFamily` by the fair-coin `chaumPedersenProbFamily` in
Experiment 0 of Attack Game 20.4 (`chvzkRealGame`) changes `Game.advantage` by at most `1 / 2 ^ n`
against every adversary (including computationally unbounded ones). -/
theorem advantage_chvzkRealGame_chaumPedersenProbFamily_le {σ : Type} (setup : ℕ → PMF F.Desc)
    (A : CHVZKAdversary (ℕ × F.Desc) (fun i => ZMod (F.order i.2))
      (fun i => F.Carrier i.2 × F.Carrier i.2 × F.Carrier i.2)
      (fun i => F.Carrier i.2 × F.Carrier i.2)
      (fun i => ZMod (F.order i.2)) (fun i => ZMod (F.order i.2)) σ) (n : ℕ) :
    Game.advantage
      (chvzkRealGame F.chaumPedersenProbFamily
        (fun i β (u, v, w) => β • F.generator i.2 = v ∧ β • u = w)
        (fun m => (setup m).map (m, ·)) A n)
      (chvzkRealGame F.chaumPedersenFamily
        (fun i β (u, v, w) => β • F.generator i.2 = v ∧ β • u = w)
        (fun m => (setup m).map (m, ·)) A n) ≤
      1 / 2 ^ n := by
  refine Game.advantage_bind_le_of_support ((setup n).map (n, ·)) _ _ fun i hi => ?_
  obtain ⟨d, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hi
  refine SigmaProtocol.advantage_chvzkExperiment_le (fun β y _ => ?_) (A n (n, d))
  rw [(F.chaumPedersenProbFamily (n, d)).conversation_eq_bind_transcript,
    (F.chaumPedersenFamily (n, d)).conversation_eq_bind_transcript]
  have hcoe : (((1 / 2 ^ n : ℝ≥0)) : ℝ≥0∞) = 1 / 2 ^ n := by
    rw [ENNReal.coe_div (pow_ne_zero _ two_ne_zero), ENNReal.coe_one, ENNReal.coe_pow,
      ENNReal.coe_ofNat]
  rw [hcoe]
  exact CloseTo.bind_right _ fun c _ =>
    ((F.closeTo_transcript_chaumPedersenProbFamily (n, d) β y c).symm).bind_left _

/-- In Attack Game 20.4 (`chvzkRealGame` vs `chvzkSimGame`), the fair-coin Chaum–Pedersen prover
`chaumPedersenProbFamily` and the strict PPT simulator `chaumPedersenSimulator` differ in
distinguishing advantage by at most `2 / 2 ^ n` against *every* adversary (including
computationally unbounded ones). Derived from `efficientSpecialHVZK_chaumPedersen_ideal` and
`advantage_chvzkRealGame_chaumPedersenProbFamily_le`. -/
theorem advantage_chvzkGame_chaumPedersenProbFamily_le {σ : Type} (setup : ℕ → PMF F.Desc)
    (A : CHVZKAdversary (ℕ × F.Desc) (fun i => ZMod (F.order i.2))
      (fun i => F.Carrier i.2 × F.Carrier i.2 × F.Carrier i.2)
      (fun i => F.Carrier i.2 × F.Carrier i.2)
      (fun i => ZMod (F.order i.2)) (fun i => ZMod (F.order i.2)) σ) (n : ℕ) :
    Game.advantage
      (chvzkRealGame F.chaumPedersenProbFamily
        (fun i β (u, v, w) => β • F.generator i.2 = v ∧ β • u = w)
        (fun m => (setup m).map (m, ·)) A n)
      (chvzkSimGame
        (fun i β (u, v, w) => β • F.generator i.2 = v ∧ β • u = w)
        (fun m => (setup m).map (m, ·)) F.chaumPedersenSimulator A n) ≤
      2 / 2 ^ n := by
  have h1 := F.advantage_chvzkRealGame_chaumPedersenProbFamily_le setup A n
  have h2 : Game.advantage
      (chvzkRealGame F.chaumPedersenFamily
        (fun i β (u, v, w) => β • F.generator i.2 = v ∧ β • u = w)
        (fun m => (setup m).map (m, ·)) A n)
      (chvzkSimGame
        (fun i β (u, v, w) => β • F.generator i.2 = v ∧ β • u = w)
        (fun m => (setup m).map (m, ·)) F.chaumPedersenSimulator A n) ≤
      1 / 2 ^ n := by
    refine F.simulatorRealizedBy_chaumPedersenSimulator.advantage_chvzkGame_le
      F.efficientSpecialHVZK_chaumPedersen_ideal.specialHVZK (fun i hi => ?_) A
    obtain ⟨d, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hi
    dsimp only
    rw [ENNReal.coe_div (pow_ne_zero _ two_ne_zero), ENNReal.coe_one, ENNReal.coe_pow,
      ENNReal.coe_ofNat]
  refine ((Game.advantage_triangle _ _ _).trans (add_le_add h1 h2)).trans_eq ?_
  ext
  push_cast
  ring

/-- **The fair-coin Chaum–Pedersen protocol satisfies computational special HVZK**
([BonehShoup2023], Theorem 19.10, Section 19.5.2, p. 777, with Definition 20.6, Section 20.4.2,
p. 840): Theorem 19.10 states exact special HVZK (Definition 19.5(ii), under Definition 2.8's
negligible-overflow runtime convention, p. 30); in the strict-PPT fair-coin model exact simulation
is impossible when `q` is not a power of two, so Definition 19.5(ii) is relaxed here to the
`2 / 2 ^ n` statistical form (`closeTo_transcript_chaumPedersenProbFamily_simulator`) and
Definition 20.6. Against the fair-coin honest prover of `chaumPedersenProbFamily`, the strict PPT
simulator `chaumPedersenSimulator` satisfies Definition 20.6 with exact zero acceptance error
(`δ = fun _ => 0`) over any group-description setup `setup : ℕ → PMF F.Desc` paired with the
security parameter. Derived from `computationalSpecialHVZK_chaumPedersen_ideal` and
`advantage_chvzkRealGame_chaumPedersenProbFamily_le`. -/
theorem computationalSpecialHVZK_chaumPedersen (setup : ℕ → PMF F.Desc) :
    ComputationalSpecialHVZK F.chaumPedersenProbFamily
      (fun i β (u, v, w) => β • F.generator i.2 = v ∧ β • u = w)
      F.chaumPedersenEncoding (fun i => F.encScalar i.2) (fun n => (setup n).map (n, ·))
      F.chaumPedersenSimulator (fun _ => 0) where
  ppt := (F.computationalSpecialHVZK_chaumPedersen_ideal setup).ppt
  accepts := (F.computationalSpecialHVZK_chaumPedersen_ideal setup).accepts
  indistinguishable encσ A hA := by
    have hideal :=
      (F.computationalSpecialHVZK_chaumPedersen_ideal setup).indistinguishable encσ A hA
    refine negligible_of_le (negligible_one_div_two_pow.add hideal) fun n => ?_
    exact (Game.advantage_triangle _ _ _).trans
      (add_le_add (F.advantage_chvzkRealGame_chaumPedersenProbFamily_le setup A n) le_rfl)

end Cslib.Crypto.PrimeOrderGroupFamily
