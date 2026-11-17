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
import CslibFrontier.Foundations.Data.ZMod.NatCast
import CslibFrontier.Tactic.PPT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip

/-!
# The Chaum–Pedersen protocol with an efficient extractor and simulator

The Chaum–Pedersen protocol for Diffie–Hellman triples ([BonehShoup2023], Section 19.5.2) over a
`PrimeOrderGroupFamily`, as a family indexed by a unary security parameter `n` and a group
description `d`, with challenges in `ZMod q` for the group order `q`. A statement is a triple
`(u, v, w)` of group elements and a witness is `β` with `β • g = v` and `β • u = w`
([BonehShoup2023], (19.12), in additive notation). Statements and commitments are framed tuples of
the family's element encoding, and scalars are binary (`chaumPedersenEncoding`).

* **Efficient special soundness** (`efficientSpecialSoundness_chaumPedersen`, Theorem 19.10 with
  Definition 19.4): the extractor `chaumPedersenExtract` computes `(c - c')⁻¹ (z - z')` with
  `extractNat`. It reads neither the statement nor the commitment, so its polynomial-time word
  function is Schnorr's `schnorrExtractWord`.
* **Efficient special HVZK** (`efficientSpecialHVZK_chaumPedersen`, Theorem 19.10 with
  Definition 19.5): Boneh and Shoup's simulator samples a uniform response `z` and outputs
  `((z • g - c • v, z • u - c • w), z)`. The typed simulator `chaumPedersenSimulator` samples `z`
  with `sampleExp`, which is within statistical distance `1 / 2 ^ n` of uniform on `ZMod q`. Its
  strict PPT certificate is the word program `chaumPedersenSimulateWord`.
* **Computational special HVZK** (`computationalSpecialHVZK_chaumPedersen`, Definition 20.6):
  every output of `chaumPedersenSimulator` is an accepting conversation
  (`accepts_chaumPedersenSimulator`), so it satisfies Definition 20.6 with zero acceptance error
  along any group-description setup.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.chaumPedersenFamily`: the protocol at each index.
* `Cslib.Crypto.PrimeOrderGroupFamily.chaumPedersenEncoding`: its word encodings.
* `Cslib.Crypto.PrimeOrderGroupFamily.chaumPedersenExtract`: the extractor.
* `Cslib.Crypto.PrimeOrderGroupFamily.chaumPedersenSimulator`,
  `Cslib.Crypto.PrimeOrderGroupFamily.chaumPedersenSimulateWord`: the simulator with `sampleExp`
  and the strict PPT word program computing it.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.efficientSpecialSoundness_chaumPedersen`
* `Cslib.Crypto.PrimeOrderGroupFamily.efficientSpecialHVZK_chaumPedersen`
* `Cslib.Crypto.PrimeOrderGroupFamily.computationalSpecialHVZK_chaumPedersen`

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 19.5.2, Theorem 19.10, Definitions 19.4, 19.5 and 20.6.
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Protocols Protocols.SigmaProtocol Interactive
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)

/-- The Chaum–Pedersen protocol ([BonehShoup2023], Section 19.5.2) in the group described by
`i.2`, with challenges in `ZMod q`. The security parameter `i.1` does not change the protocol. -/
@[expose] noncomputable def chaumPedersenFamily (i : ℕ × F.Desc) :
    SigmaProtocol (ZMod (F.order i.2)) (F.Carrier i.2 × F.Carrier i.2 × F.Carrier i.2)
      (F.Carrier i.2 × F.Carrier i.2) (ZMod (F.order i.2)) (ZMod (F.order i.2)) :=
  chaumPedersen (Function.Embedding.refl _) (F.generator i.2)

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
    Function.Embedding.coeFn_mk, encNat_apply, ZMod.val_natCast, encPair_apply,
    encBits_apply]

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
    (ComputableInPolyTime.binary_mod' hs hq).of_enc_eq
      fun _ => (Cslib.Encoding.encNat_eq_bits _).symm
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

/-- **The Chaum–Pedersen protocol has efficient special HVZK** ([BonehShoup2023], Theorem 19.10
with Definition 19.5), with statistical error `1 / 2 ^ n` at security parameter `n`: the perfect
simulator `linearSimulate` is realized by the strict PPT simulator `chaumPedersenSimulator`. -/
theorem efficientSpecialHVZK_chaumPedersen :
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

/-- **The Chaum–Pedersen protocol has computational special HVZK** ([BonehShoup2023],
Definition 20.6) with zero acceptance error (`δ = fun _ => 0`) over any group-description setup
`setup : ℕ → PMF F.Desc` paired with the security parameter. -/
theorem computationalSpecialHVZK_chaumPedersen (setup : ℕ → PMF F.Desc) :
    ComputationalSpecialHVZK F.chaumPedersenFamily
      (fun i β (u, v, w) => β • F.generator i.2 = v ∧ β • u = w)
      F.chaumPedersenEncoding (fun i => F.encScalar i.2) (fun n => (setup n).map (n, ·))
      F.chaumPedersenSimulator (fun _ => 0) :=
  F.simulatorRealizedBy_chaumPedersenSimulator.computationalSpecialHVZK_of_accepts
    (fun _ => chaumPedersen_specialHVZK) F.isPPT_chaumPedersenSimulator
    (fun i y c => by rw [F.accepts_chaumPedersenSimulator i y c, tsub_zero])
    (exists_negligible_inv_two_pow_map setup)

end Cslib.Crypto.PrimeOrderGroupFamily
