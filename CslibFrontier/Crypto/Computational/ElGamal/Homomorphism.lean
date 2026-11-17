/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
public import CslibFrontier.Crypto.Computational.ElGamal.Decodable
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Crypto.Game.FourHop
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Foundations.Data.Nat.Bits
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.SuppCases

/-!
# Homomorphism of Multiplicative ElGamal and Equivalence of Semantic Security with DDH

Multiplicative ElGamal ([BonehShoup2023], Exercise 11.5, printed p. 459) encrypts a group element
`m : F.Carrier d` under public key `u = α • g` as `(v, e) = (β • g, β • u + m)` (written additively
on `F.Carrier d`, matching `CslibFrontier/Crypto/Computational/ElGamal.lean`) and decrypts `(v, e)`
to `e - α • v`. This module formalizes parts (b) and (c) of Exercise 11.5:

1. **Homomorphic ciphertext combination ([BonehShoup2023], Exercise 11.5(c), p. 459):**
   Adding two algebraic ciphertexts on `F.Carrier d × F.Carrier d` adds both their plaintexts and
   their randomness exponents (`elGamalEncrypt_add`), and decryption is a homomorphism
   (`elGamalDecrypt_add`). On encoded ciphertexts, `elGamalAddCiphertext` applies `F.add` to the two
   framed components in polynomial time (`computableInPolyTime_elGamalAddCiphertext`). Because every
   canonical residue below `F.order (d n)` lies in the support of `F.sampleExp n (d n)`, combining
   any two ciphertexts in the support of `elGamalEncryptProb` under an honest public key produces a
   ciphertext in the support of `elGamalEncryptProb` for `m₁ + m₂`
   (`elGamalAddCiphertext_mem_support_elGamalEncryptProb`) that decrypts to `encode (m₁ + m₂)`
   (`elGamalDecryptDet_elGamalAddCiphertext`).

2. **Semantic security implies DDH ([BonehShoup2023], Exercise 11.5(b), p. 459):**
   Given a word-level DDH distinguisher `W` and an extractor `descOf` recovering `d` from `(n, pk)`,
   the two-stage adversary `ddhWordToElGamalAdversary descOf W` samples `c ← F.sampleExp n d`,
   submits the challenge pair `(encode 0, encode (c • g))` with saved state `pk`, and runs `W` on
   the public key and challenge ciphertext components `(d, u, v, e)`. In world `false`, the unused
   draw `c` drops out and `(u, v, e) = (α • g, β • g, (α * β) • g)` reproduces `ddhRealGame`
   (`ddhRealGame_eq_elGamalGroupCPAGameOn_false`). In world `true`, `e = (α * β) • g + c • g` is
   within statistical distance `1 / 2 ^ n` of a uniform group element (`ddhRandomGame`,
   `advantage_elGamalGroupCPAGameOn_true_ddhRandomGame_le`), and within `5 / 2 ^ n` in the native
   `Encryption.gameOn` experiment (`advantage_ddhGame_le_gameOn`, adding `2 / 2 ^ n` in each world
   for `elGamalKeyGenProb` and `elGamalEncryptProb`). Through `ddh_iff_encoded`, semantic security
   therefore implies `F.DDH` (`ddh_of_negligible_elGamalGroupCPAGameOn`,
   `ddh_of_indcpaOn_elGamalGroupEncryptProb`), yielding the two-sided characterizations
   `negligible_elGamalGroupCPAGame_iff_ddh` and `indcpaOn_elGamalGroupEncryptProb_iff_ddh` over a
   `DecodablePrimeOrderGroupFamily`. Callers obtain the contrapositive `¬ DDH → ¬ INDCPAOn` via
   `mt`, e.g. `mt (F.indcpaOn_elGamalGroupEncryptProb_iff_ddh hd).mp`.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalAddCiphertext`: polynomial-time componentwise addition
  of encoded multiplicative ElGamal ciphertexts ([BonehShoup2023], Exercise 11.5(c), p. 459).
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhWordToElGamalAdversary`: chosen-plaintext adversary
  reducing word-level DDH to group-element multiplicative ElGamal IND-CPA ([BonehShoup2023],
  Exercise 11.5(b), p. 459).

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalEncrypt_add`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalDecrypt_add`: algebraic homomorphisms of ElGamal
  encryption and decryption.
* `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_elGamalAddCiphertext`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalAddCiphertext_encodeElGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalAddCiphertext_mem_support_elGamalEncryptProb`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalDecryptDet_elGamalAddCiphertext`: polynomial-time
  word-level homomorphism, support closure on `elGamalEncryptProb`, and decryption correctness
  ([BonehShoup2023], Exercise 11.5(c), p. 459).
* `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_ddhWordToElGamalAdversary`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhRealGame_eq_elGamalGroupCPAGameOn_false`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_elGamalGroupCPAGameOn_true_ddhRandomGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_ddhGame_le_elGamalGroupCPAGameOn`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_ddhGame_le_gameOn`: uniform strict-PPT certificate
  and concrete DDH advantage bounds for `ddhWordToElGamalAdversary`.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddh_of_negligible_elGamalGroupCPAGameOn`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddh_of_indcpaOn_elGamalGroupEncryptProb`: group-element
  ElGamal CPA security implies DDH ([BonehShoup2023], Exercise 11.5(b), p. 459).
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.negligible_elGamalGroupCPAGame_iff_ddh`,
  `Cslib.Crypto.DecodablePrimeOrderGroupFamily.indcpaOn_elGamalGroupEncryptProb_iff_ddh`:
  equivalence between group-element ElGamal IND-CPA security and DDH ([BonehShoup2023],
  Exercise 11.5(a)–(b), p. 459).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Exercise 11.5(a)–(c) (printed p. 459).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM Encryption
open scoped NNReal

namespace PrimeOrderGroupFamily

variable (F : PrimeOrderGroupFamily)

/-! ### Multiplicative homomorphism ([BonehShoup2023], Exercise 11.5(c)) -/

/-- **Algebraic homomorphism of multiplicative ElGamal encryption** ([BonehShoup2023],
Exercise 11.5(c), p. 459, written additively): componentwise addition of two ciphertexts under the
same public key `u` yields the encryption of `m₁ + m₂` with randomness `β₁ + β₂`. -/
theorem elGamalEncrypt_add (d : F.Desc) (u m₁ m₂ : F.Carrier d)
    (β₁ β₂ : ZMod (F.order d)) :
    F.elGamalEncrypt d u m₁ β₁ + F.elGamalEncrypt d u m₂ β₂ =
      F.elGamalEncrypt d u (m₁ + m₂) (β₁ + β₂) := by
  simp only [elGamalEncrypt, Prod.mk_add_mk, add_smul]
  exact Prod.ext rfl (add_add_add_comm _ _ _ _)

/-- **Algebraic homomorphism of multiplicative ElGamal decryption** ([BonehShoup2023],
Exercise 11.5(c), p. 459, written additively): decrypting the sum of two ciphertexts equals the sum
of their decryptions. -/
theorem elGamalDecrypt_add (d : F.Desc) (α : ZMod (F.order d))
    (ct₁ ct₂ : F.Carrier d × F.Carrier d) :
    F.elGamalDecrypt d α (ct₁ + ct₂) =
      F.elGamalDecrypt d α ct₁ + F.elGamalDecrypt d α ct₂ := by
  simp only [elGamalDecrypt, Prod.fst_add, Prod.snd_add, smul_add]
  exact add_sub_add_comm _ _ _ _

/-- Word-level homomorphic ciphertext combination for multiplicative ElGamal ([BonehShoup2023],
Exercise 11.5(c), p. 459): add both framed group-element components of `ct₁` and `ct₂` using
`F.add`. -/
@[expose] def elGamalAddCiphertext (d : F.Desc) (ct₁ ct₂ : List Bool) : List Bool :=
  encPair encBits encBits
    (F.add (d, unframe ct₁, unframe ct₂), F.add (d, dropFrame ct₁, dropFrame ct₂))

/-- On encoded group elements, `elGamalAddCiphertext` adds both ciphertext components in
`F.Carrier d`. -/
theorem elGamalAddCiphertext_encode (d : F.Desc) (v₁ e₁ v₂ e₂ : F.Carrier d) :
    F.elGamalAddCiphertext d
      (encPair encBits encBits (F.encode d v₁, F.encode d e₁))
      (encPair encBits encBits (F.encode d v₂, F.encode d e₂)) =
      encPair encBits encBits (F.encode d (v₁ + v₂), F.encode d (e₁ + e₂)) := by
  simp only [elGamalAddCiphertext, unframe_encPair_encBits, dropFrame_encPair_encBits,
    F.add_encode]

/-- `elGamalAddCiphertext` is computable in polynomial time. -/
theorem computableInPolyTime_elGamalAddCiphertext :
    ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool => F.elGamalAddCiphertext p.1 p.2.1 p.2.2)
      (encPair F.encDesc (encPair encBits encBits)) encBits := by
  have hd := ComputableInPolyTime.fst F.encDesc (encPair encBits encBits)
  have hcts := ComputableInPolyTime.snd F.encDesc (encPair encBits encBits)
  have hct₁ := (ComputableInPolyTime.fst encBits encBits).comp hcts
  have hct₂ := (ComputableInPolyTime.snd encBits encBits).comp hcts
  have hv := F.computableInPolyTime_add.comp
    (hd.prod ((ComputableInPolyTime.unframe.comp hct₁).prod
      (ComputableInPolyTime.unframe.comp hct₂)))
  have he := F.computableInPolyTime_add.comp
    (hd.prod ((ComputableInPolyTime.dropFrame.comp hct₁).prod
      (ComputableInPolyTime.dropFrame.comp hct₂)))
  exact (hv.prod he).encoding_comp

/-- **Word-level encryption homomorphism** ([BonehShoup2023], Exercise 11.5(c), p. 459): combining
two `encodeElGamalEncrypt` ciphertexts under `encode u` with exponents `b₁, b₂ : ℕ` yields the
`encodeElGamalEncrypt` ciphertext for `m₁ + m₂` with exponent `b₁ + b₂`. -/
theorem elGamalAddCiphertext_encodeElGamalEncrypt (d : F.Desc) (u m₁ m₂ : F.Carrier d)
    (b₁ b₂ : ℕ) :
    F.elGamalAddCiphertext d
      (encPair encBits encBits (F.encodeElGamalEncrypt (d, F.encode d u, F.encode d m₁, b₁)))
      (encPair encBits encBits (F.encodeElGamalEncrypt (d, F.encode d u, F.encode d m₂, b₂))) =
      encPair encBits encBits
        (F.encodeElGamalEncrypt (d, F.encode d u, F.encode d (m₁ + m₂), b₁ + b₂)) := by
  simp only [encodeElGamalEncrypt_encode, elGamalAddCiphertext_encode, ← Prod.fst_add,
    ← Prod.snd_add, elGamalEncrypt_add, Nat.cast_add]

/-- Every canonical exponent `r < F.order d` lies in the support of `F.sampleExp n d`, because
`F.order d < 2 ^ |encNat (F.order d)| ≤ 2 ^ (n + |encNat (F.order d)|)` and `r % F.order d = r`. -/
private theorem mem_support_sampleExp_of_lt (n : ℕ) (d : F.Desc) {r : ℕ} (hr : r < F.order d) :
    r ∈ (ProbComp.eval (F.sampleExp n d)).support := by
  have hord : F.order d < 2 ^ (encNat (F.order d)).length := by
    simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.lt_size_self (F.order d)
  have hlt : r < 2 ^ (n + (encNat (F.order d)).length) :=
    (hr.trans hord).trans_le (Nat.pow_le_pow_right (by omega) (Nat.le_add_left _ _))
  simp only [sampleExp, ProbComp.sampleModNat, ProbComp.eval_map, PMF.mem_support_map_iff]
  exact ⟨r, (ProbComp.mem_support_sampleBinaryNat_iff _ r).mpr hlt, Nat.mod_eq_of_lt hr⟩

/-- **Homomorphic support closure on `elGamalEncryptProb`** ([BonehShoup2023], Exercise 11.5(c),
p. 459): for any honest key pair `(pk, sk)` in the support of `elGamalKeyGenProb d n` and any
ciphertexts `ct₁`, `ct₂` in the supports of `elGamalEncryptProb` for `encode m₁` and `encode m₂`,
`elGamalAddCiphertext (d n) ct₁ ct₂` lies in the support of `elGamalEncryptProb` for
`encode (m₁ + m₂)`. -/
theorem elGamalAddCiphertext_mem_support_elGamalEncryptProb (d : ℕ → F.Desc) (n : ℕ)
    {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (F.elGamalKeyGenProb d n)).support)
    {m₁ m₂ : F.Carrier (d n)} {ct₁ ct₂ : List Bool}
    (hct₁ : ct₁ ∈ (ProbComp.eval
      (F.elGamalEncryptProb (fun _ x => x) d n keys.1 (F.encode (d n) m₁))).support)
    (hct₂ : ct₂ ∈ (ProbComp.eval
      (F.elGamalEncryptProb (fun _ x => x) d n keys.1 (F.encode (d n) m₂))).support) :
    F.elGamalAddCiphertext (d n) ct₁ ct₂ ∈ (ProbComp.eval
      (F.elGamalEncryptProb (fun _ x => x) d n keys.1 (F.encode (d n) (m₁ + m₂)))).support := by
  supp_cases hkeys [elGamalKeyGenProb] with ⟨a, _, rfl⟩
  supp_cases hct₁ [elGamalEncryptProb] with ⟨b₁, _, rfl⟩
  supp_cases hct₂ [elGamalEncryptProb] with ⟨b₂, _, rfl⟩
  simp only [elGamalEncryptProb, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff, dropFrame_encPair_encBits, encodeElGamalPublicKey_eq_encode]
  refine ⟨(b₁ + b₂) % F.order (d n),
    F.mem_support_sampleExp_of_lt n (d n) (Nat.mod_lt _ (F.prime_order (d n)).pos), ?_⟩
  rw [F.elGamalAddCiphertext_encodeElGamalEncrypt]
  simp only [encodeElGamalEncrypt_encode, ZMod.natCast_mod]

/-- **Decryption of homomorphically combined `elGamalEncryptProb` ciphertexts**
([BonehShoup2023], Exercise 11.5(c), p. 459): for any honest key pair `(pk, sk)` and honest
encryptions `ct₁`, `ct₂` of `encode m₁`, `encode m₂`, decrypting
`elGamalAddCiphertext (d n) ct₁ ct₂` recovers `encode (m₁ + m₂)`. -/
theorem elGamalDecryptDet_elGamalAddCiphertext (d : ℕ → F.Desc) (n : ℕ)
    {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (F.elGamalKeyGenProb d n)).support)
    {m₁ m₂ : F.Carrier (d n)} {ct₁ ct₂ : List Bool}
    (hct₁ : ct₁ ∈ (ProbComp.eval
      (F.elGamalEncryptProb (fun _ x => x) d n keys.1 (F.encode (d n) m₁))).support)
    (hct₂ : ct₂ ∈ (ProbComp.eval
      (F.elGamalEncryptProb (fun _ x => x) d n keys.1 (F.encode (d n) m₂))).support) :
    F.elGamalDecryptDet d n keys.2 (F.elGamalAddCiphertext (d n) ct₁ ct₂) =
      F.encode (d n) (m₁ + m₂) :=
  F.elGamalDecryptDet_elGamalEncryptProb d n hkeys (m₁ + m₂)
    (F.elGamalAddCiphertext_mem_support_elGamalEncryptProb d n hkeys hct₁ hct₂)

/-! ### Semantic security implies DDH ([BonehShoup2023], Exercise 11.5(b)) -/

/-- Chosen-plaintext adversary reducing word-level DDH to group-element multiplicative ElGamal
([BonehShoup2023], Exercise 11.5(b), p. 459): given `descOf` recovering the group description `d`
from `(n, pk)` and a word-level DDH distinguisher `W`, `choose` samples `c ← F.sampleExp n d` and
submits `(encode 0, encode (c • g))` with saved state `pk`, and `guess` runs `W` on `(d, u, v, e)`
where `u = dropFrame pk`, `v = unframe ct`, and `e = dropFrame ct`. -/
noncomputable def ddhWordToElGamalAdversary (descOf : ℕ → List Bool → F.Desc)
    (W : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool) :
    Encryption.WordAdversary where
  choose n pk := do
    let d := descOf n pk
    let c ← F.sampleExp n d
    return ((F.encode d 0, F.smul (d, c, F.encode d (F.generator d))), pk)
  guess n pk ct :=
    W n (descOf n pk, dropFrame pk, unframe ct, dropFrame ct)

/-- `ddhWordToElGamalAdversary` is uniform strict PPT whenever `descOf` is computable in polynomial
time and `W` is uniform strict PPT. -/
theorem isPPT_ddhWordToElGamalAdversary {descOf : ℕ → List Bool → F.Desc}
    {W : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool}
    (hdesc : ComputableInPolyTime (fun p : ℕ × List Bool => descOf p.1 p.2)
      (encPair encUnary encBits) F.encDesc)
    (hW : IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun x => W x.1 x.2)) :
    (F.ddhWordToElGamalAdversary descOf W).IsPPT := by
  let E0 := encPair encUnary encBits
  have hp := ComputableInPolyTime.fst E0 encNat
  have hc := ComputableInPolyTime.snd E0 encNat
  have hd := hdesc.comp hp
  have hm₀ := computableInPolyTime_encode_zero hd
  have hm₁ := F.computableInPolyTime_smul.comp
    (hd.prod (hc.prod (F.computableInPolyTime_generator.comp hd)))
  have hpk0 := (ComputableInPolyTime.snd encUnary encBits).comp hp
  have hchoose : Probability.IsPPT (encChoiceOut encBits)
      (F.ddhWordToElGamalAdversary descOf W).choose :=
    ((F.isPPTOn_sampleExp (ComputableInPolyTime.fst encUnary encBits) hdesc).bind_with
      (((hm₀.prod hm₁).prod hpk0).isPPTOn)).isPPT
  have hn := ComputableInPolyTime.fst encUnary (encPair encBits encBits)
  have hrest := ComputableInPolyTime.snd encUnary (encPair encBits encBits)
  have hpk := (ComputableInPolyTime.fst encBits encBits).comp hrest
  have hct := (ComputableInPolyTime.snd encBits encBits).comp hrest
  have hguess : IsPPTOn encGuessInput encBool
      (fun ⟨n, state, ciphertext⟩ =>
        (F.ddhWordToElGamalAdversary descOf W).guess n state ciphertext) :=
    hW.preprocess
      (hn.prod ((hdesc.comp (hn.prod hpk)).prod
        ((ComputableInPolyTime.dropFrame.comp hpk).prod
          ((ComputableInPolyTime.unframe.comp hct).prod
            (ComputableInPolyTime.dropFrame.comp hct)))))
  exact ⟨hchoose, hguess⟩

/-- In world `false` (`m₀ = 0`), `ddhWordToElGamalAdversary` ignores its sampled exponent `c` and
passes `(α • g, β • g, (α * β) • g)` to `W`, matching `ddhRealGame` with zero sampling loss. -/
theorem ddhRealGame_eq_elGamalGroupCPAGameOn_false
    (valid : ℕ → List Bool → List Bool → List Bool → Bool) (setup : ℕ → PMF F.Desc)
    (descOf : ℕ → List Bool → F.Desc)
    (W : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool) (n : ℕ)
    (hdesc_eq : ∀ d ∈ (setup n).support, ∀ u,
      descOf n (encPair F.encDesc encBits (d, u)) = d)
    (hvalid : ∀ d ∈ (setup n).support, ∀ u m₀ m₁ : F.Carrier d,
      valid n (encPair F.encDesc encBits (d, F.encode d u))
        (F.encode d m₀) (F.encode d m₁) = true) :
    F.ddhRealGame setup (fun n d u v w => W n (d, F.encode d u, F.encode d v, F.encode d w)) n =
      F.elGamalGroupCPAGameOn valid setup (F.ddhWordToElGamalAdversary descOf W) false n := by
  simp only [ddhRealGame, Game.withSetup, eval_ddhRealExperiment, elGamalGroupCPAGameOn,
    elGamalMsgCPAGameOn, elGamalMsgCPAGameWith, ddhWordToElGamalAdversary, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
    PMF.pure_bind, ChoiceOut.msg₀, ChoiceOut.msg₁, ChoiceOut.msgs, Bool.false_eq_true, ↓reduceIte]
  refine PMF.bind_congr_on_support _ _ _ fun d hd => ?_
  refine congrArg (PMF.bind _) (funext fun α => ?_)
  rw [hdesc_eq d hd]
  simp only [F.smul_encode, hvalid d hd, ↓reduceIte, F.add_encode, add_zero,
    dropFrame_encPair_encBits, unframe_encPair_encBits, PMF.bind_const]

/-- In world `true` (`m₁ = c • g`), `ddhWordToElGamalAdversary` masks `(α * β) • g` by `c • g` for
`c ← F.sampleExp n d`, matching `ddhRandomGame` within statistical distance `1 / 2 ^ n`. -/
theorem advantage_elGamalGroupCPAGameOn_true_ddhRandomGame_le
    (valid : ℕ → List Bool → List Bool → List Bool → Bool) (setup : ℕ → PMF F.Desc)
    (descOf : ℕ → List Bool → F.Desc)
    (W : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool) (n : ℕ)
    (hdesc_eq : ∀ d ∈ (setup n).support, ∀ u,
      descOf n (encPair F.encDesc encBits (d, u)) = d)
    (hvalid : ∀ d ∈ (setup n).support, ∀ u m₀ m₁ : F.Carrier d,
      valid n (encPair F.encDesc encBits (d, F.encode d u))
        (F.encode d m₀) (F.encode d m₁) = true) :
    Game.advantage
      (F.elGamalGroupCPAGameOn valid setup (F.ddhWordToElGamalAdversary descOf W) true n)
      (F.ddhRandomGame setup
        (fun n d u v w => W n (d, F.encode d u, F.encode d v, F.encode d w)) n) ≤
      1 / 2 ^ n := by
  simp only [elGamalGroupCPAGameOn, elGamalMsgCPAGameOn, elGamalMsgCPAGameWith, ddhRandomGame,
    Game.withSetup, eval_ddhRandomExperiment, ddhWordToElGamalAdversary, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
    PMF.pure_bind, ChoiceOut.msg₀, ChoiceOut.msg₁, ChoiceOut.msgs, ↓reduceIte]
  refine Game.advantage_bind_le_of_support (setup n) _ _ fun d hd => ?_
  refine Game.advantage_bind_le_nnreal _ _ _ fun α => ?_
  rw [hdesc_eq d hd]
  simp only [F.smul_encode, hvalid d hd, ↓reduceIte, F.add_encode,
    dropFrame_encPair_encBits, unframe_encPair_encBits]
  rw [PMF.bind_comm]
  refine Game.advantage_bind_le_nnreal _ _ _ fun β => ?_
  have hmask := F.uniform_smul_generator_add d ((α * β) • F.generator d)
    (fun z => ProbComp.eval
      (W n (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d), F.encode d z)))
  rw [← hmask]
  simp only [add_comm ((α * β) • F.generator d)]
  exact F.advantage_bind_sampleExp_le n d fun γ => ProbComp.eval
    (W n (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d),
      F.encode d (γ • F.generator d + (α * β) • F.generator d)))

/-- **Quantitative reduction from word-level DDH to `elGamalGroupCPAGameOn`**
([BonehShoup2023], Exercise 11.5(b), p. 459): the DDH advantage of `W` is at most the CPA advantage
of `ddhWordToElGamalAdversary descOf W` plus `1 / 2 ^ n`. -/
theorem advantage_ddhGame_le_elGamalGroupCPAGameOn
    (valid : ℕ → List Bool → List Bool → List Bool → Bool) (setup : ℕ → PMF F.Desc)
    (descOf : ℕ → List Bool → F.Desc)
    (W : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool) (n : ℕ)
    (hdesc_eq : ∀ d ∈ (setup n).support, ∀ u,
      descOf n (encPair F.encDesc encBits (d, u)) = d)
    (hvalid : ∀ d ∈ (setup n).support, ∀ u m₀ m₁ : F.Carrier d,
      valid n (encPair F.encDesc encBits (d, F.encode d u))
        (F.encode d m₀) (F.encode d m₁) = true) :
    Game.advantage
      (F.ddhRealGame setup
        (fun n d u v w => W n (d, F.encode d u, F.encode d v, F.encode d w)) n)
      (F.ddhRandomGame setup
        (fun n d u v w => W n (d, F.encode d u, F.encode d v, F.encode d w)) n) ≤
      Game.advantage
        (F.elGamalGroupCPAGameOn valid setup (F.ddhWordToElGamalAdversary descOf W) false n)
        (F.elGamalGroupCPAGameOn valid setup (F.ddhWordToElGamalAdversary descOf W) true n) +
      1 / 2 ^ n := by
  rw [F.ddhRealGame_eq_elGamalGroupCPAGameOn_false valid setup descOf W n hdesc_eq hvalid]
  exact (Game.advantage_triangle _
    (F.elGamalGroupCPAGameOn valid setup (F.ddhWordToElGamalAdversary descOf W) true n) _).trans
    (add_le_add le_rfl
      (F.advantage_elGamalGroupCPAGameOn_true_ddhRandomGame_le valid setup descOf W n
        hdesc_eq hvalid))

/-- **Quantitative reduction from word-level DDH to native `Encryption.gameOn`**
([BonehShoup2023], Exercise 11.5(b), p. 459): on a parameterized group family `d : ℕ → F.Desc`,
combining `advantage_ddhGame_le_elGamalGroupCPAGameOn` (`1 / 2 ^ n`) with the two `2 / 2 ^ n`
bridges of `advantage_gameOn_elGamalMsgCPAGameOn_le` bounds DDH advantage by native CPA advantage
plus `5 / 2 ^ n`. -/
theorem advantage_ddhGame_le_gameOn
    (valid : ℕ → List Bool → List Bool → List Bool → Bool) (d : ℕ → F.Desc)
    (W : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool) (n : ℕ)
    (hvalid : ∀ u m₀ m₁ : F.Carrier (d n),
      valid n (encPair F.encDesc encBits (d n, F.encode (d n) u))
        (F.encode (d n) m₀) (F.encode (d n) m₁) = true) :
    Game.advantage
      (F.ddhRealGame (fun m => PMF.pure (d m))
        (fun n d u v w => W n (d, F.encode d u, F.encode d v, F.encode d w)) n)
      (F.ddhRandomGame (fun m => PMF.pure (d m))
        (fun n d u v w => W n (d, F.encode d u, F.encode d v, F.encode d w)) n) ≤
      Game.advantage
        (ProbComp.eval (gameOn valid (F.elGamalKeyGenProb d)
          (F.elGamalEncryptProb (fun _ m => m) d)
          (F.ddhWordToElGamalAdversary (fun m _ => d m) W) false n))
        (ProbComp.eval (gameOn valid (F.elGamalKeyGenProb d)
          (F.elGamalEncryptProb (fun _ m => m) d)
          (F.ddhWordToElGamalAdversary (fun m _ => d m) W) true n)) +
      5 / 2 ^ n := by
  let adv := F.ddhWordToElGamalAdversary (fun m _ => d m) W
  have hddh := F.advantage_ddhGame_le_elGamalGroupCPAGameOn valid (fun m => PMF.pure (d m))
    (fun m _ => d m) W n (fun d' hd' _ => by
      simp only [PMF.support_pure, Set.mem_singleton_iff] at hd'
      exact hd'.symm)
    (fun d' hd' u m₀ m₁ => by
      simp only [PMF.support_pure, Set.mem_singleton_iff] at hd'
      subst hd'
      exact hvalid u m₀ m₁)
  have hhop₀ := (Game.advantage_comm _ _).trans_le
    (F.advantage_gameOn_elGamalMsgCPAGameOn_le valid (fun _ m => m) d adv false n)
  have hhop₁ := (Game.advantage_comm _ _).trans_le
    (F.advantage_gameOn_elGamalMsgCPAGameOn_le valid (fun _ m => m) d adv true n)
  have hcpa := Game.advantage_four_hop_le hhop₀ hhop₁
  exact hddh.trans ((add_le_add hcpa le_rfl).trans_eq (by ring))

/-- **Group-element ElGamal CPA security in `elGamalGroupCPAGameOn` implies DDH**
([BonehShoup2023], Exercise 11.5(b), p. 459): given a total polynomial-time decoder `decDesc` for
`F.encDesc` and an admissibility predicate `valid` that admits all pairs of encoded group elements
on `setup`, negligible advantage for every PPT `WordAdversary` implies `F.DDH setup`. The
contrapositive `¬ F.DDH setup → ¬ (∀ adversary, …)` follows via `mt`. -/
theorem ddh_of_negligible_elGamalGroupCPAGameOn {setup : ℕ → PMF F.Desc}
    {valid : ℕ → List Bool → List Bool → List Bool → Bool}
    (decDesc : Decoder F.encDesc)
    (hvalid : ∀ n, ∀ d ∈ (setup n).support, ∀ u m₀ m₁ : F.Carrier d,
      valid n (encPair F.encDesc encBits (d, F.encode d u))
        (F.encode d m₀) (F.encode d m₁) = true)
    (hcpa : ∀ adversary : Encryption.WordAdversary, adversary.IsPPT →
      Negligible fun n =>
        Game.advantage (F.elGamalGroupCPAGameOn valid setup adversary false n)
          (F.elGamalGroupCPAGameOn valid setup adversary true n)) :
    F.DDH setup := by
  rw [F.ddh_iff_encoded]
  intro W hW
  let descOf : ℕ → List Bool → F.Desc := fun _ pk => decDesc.decode (unframe pk)
  have hdesc : ComputableInPolyTime (fun p : ℕ × List Bool => descOf p.1 p.2)
      (encPair encUnary encBits) F.encDesc :=
    decDesc.computableInPolyTime.comp
      (ComputableInPolyTime.unframe.comp (ComputableInPolyTime.snd encUnary encBits))
  have hneg := hcpa _ (F.isPPT_ddhWordToElGamalAdversary (descOf := descOf) hdesc hW)
  have h1 : Negligible fun n => (1 : ℝ≥0) / 2 ^ n := by
    simpa only [Nat.cast_one] using negligible_const_div_two_pow 1
  refine negligible_of_le (hneg.add h1) fun n => ?_
  dsimp only [Pi.add_apply]
  exact F.advantage_ddhGame_le_elGamalGroupCPAGameOn valid setup descOf W n
    (fun d _ u => by simp only [descOf, unframe_encPair, decDesc.decode_enc]) (hvalid n)

/-- **Native `INDCPAOn` security of group-element multiplicative ElGamal implies DDH**
([BonehShoup2023], Exercise 11.5(b), p. 459): for a polynomial-time group description family
`d : ℕ → F.Desc` and any admissibility predicate `valid` admitting all pairs of encoded group
elements at `d n`, `INDCPAOn valid encBits (F.elGamalKeyGenProb d) (F.elGamalEncryptProb
(fun _ m => m) d)` implies `F.DDH (fun n => PMF.pure (d n))` (without needing a decoder for
`F.encDesc` or `DecodablePrimeOrderGroupFamily`). Callers obtain `¬ DDH → ¬ INDCPAOn` via `mt`. -/
theorem ddh_of_indcpaOn_elGamalGroupEncryptProb {d : ℕ → F.Desc}
    {valid : ℕ → List Bool → List Bool → List Bool → Bool}
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hvalid : ∀ n (u m₀ m₁ : F.Carrier (d n)),
      valid n (encPair F.encDesc encBits (d n, F.encode (d n) u))
        (F.encode (d n) m₀) (F.encode (d n) m₁) = true)
    (hcpa : INDCPAOn valid encBits (F.elGamalKeyGenProb d)
      (F.elGamalEncryptProb (fun _ m => m) d)) :
    F.DDH (fun n => PMF.pure (d n)) := by
  rw [F.ddh_iff_encoded]
  intro W hW
  have hdesc : ComputableInPolyTime (fun p : ℕ × List Bool => d p.1)
      (encPair encUnary encBits) F.encDesc :=
    hd.comp (ComputableInPolyTime.fst encUnary encBits)
  have hneg := hcpa _ (F.isPPT_ddhWordToElGamalAdversary (descOf := fun m _ => d m) hdesc hW)
  have h5 : Negligible fun n => (5 : ℝ≥0) / 2 ^ n := by
    simpa only [Nat.cast_ofNat] using negligible_const_div_two_pow 5
  refine negligible_of_le (hneg.add h5) fun n => ?_
  dsimp only [Pi.add_apply]
  exact F.advantage_ddhGame_le_gameOn valid d W n (hvalid n)

end PrimeOrderGroupFamily

namespace DecodablePrimeOrderGroupFamily

variable (F : DecodablePrimeOrderGroupFamily)

/-- **Group-element multiplicative ElGamal CPA security in `elGamalGroupCPAGame` is equivalent to
DDH** ([BonehShoup2023], Exercise 11.5(a)–(b), p. 459) over a `DecodablePrimeOrderGroupFamily`
equipped with a total polynomial-time decoder `decDesc : Decoder F.encDesc`, for any setup law
`setup : ℕ → PMF F.Desc`. Callers obtain `¬ DDH → ¬ (…) ` via `mt … .mp`. -/
theorem negligible_elGamalGroupCPAGame_iff_ddh (setup : ℕ → PMF F.Desc)
    (decDesc : Decoder F.encDesc) :
    (∀ adversary : Encryption.WordAdversary, adversary.IsPPT →
      Negligible fun n =>
        Game.advantage (F.elGamalGroupCPAGame setup adversary false n)
          (F.elGamalGroupCPAGame setup adversary true n)) ↔
      F.toPrimeOrderGroupFamily.DDH setup := by
  refine ⟨fun hcpa => ?_, fun hDDH _ hA => DDH.negligible_elGamalGroupCPAGame hDDH hA⟩
  have hgame (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ) :
      F.toPrimeOrderGroupFamily.elGamalGroupCPAGameOn
        (fun _ pk m₀ m₁ =>
          F.isElem (decDesc.decode (unframe pk), m₀) &&
            F.isElem (decDesc.decode (unframe pk), m₁))
        setup adversary bit n =
        F.elGamalGroupCPAGame setup adversary bit n := by
    simp only [PrimeOrderGroupFamily.elGamalGroupCPAGameOn,
      PrimeOrderGroupFamily.elGamalMsgCPAGameOn, elGamalGroupCPAGame,
      PrimeOrderGroupFamily.elGamalMsgCPAGameWith, unframe_encPair, decDesc.decode_enc]
  refine F.toPrimeOrderGroupFamily.ddh_of_negligible_elGamalGroupCPAGameOn decDesc
    (valid := fun _ pk m₀ m₁ =>
      F.isElem (decDesc.decode (unframe pk), m₀) &&
        F.isElem (decDesc.decode (unframe pk), m₁))
    (fun _ d _ _ m₀ m₁ => by
      simp only [unframe_encPair, decDesc.decode_enc, F.isElem_encode, Bool.and_self])
    fun adversary hA => ?_
  simpa only [hgame] using hcpa adversary hA

/-- **Native `Encryption.INDCPAOn` security of group-element multiplicative ElGamal is equivalent
to DDH** ([BonehShoup2023], Exercise 11.5(a)–(b), p. 459): for any `DecodablePrimeOrderGroupFamily`
and polynomial-time group description family `d : ℕ → F.Desc`, `(F.elGamalKeyGenProb d,
F.elGamalEncryptProb (fun _ m => m) d)` satisfies `INDCPAOn (F.elGamalGroupValid d) encBits` if and
only if `F.toPrimeOrderGroupFamily.DDH (fun n => PMF.pure (d n))` holds. When DDH fails in `d`,
multiplicative ElGamal is not semantically secure (`mt (F.indcpaOn_elGamalGroupEncryptProb_iff_ddh
hd).mp`). -/
theorem indcpaOn_elGamalGroupEncryptProb_iff_ddh {d : ℕ → F.Desc}
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    INDCPAOn (F.elGamalGroupValid d) encBits (F.elGamalKeyGenProb d)
        (F.elGamalEncryptProb (fun _ m => m) d) ↔
      F.toPrimeOrderGroupFamily.DDH (fun n => PMF.pure (d n)) :=
  ⟨F.toPrimeOrderGroupFamily.ddh_of_indcpaOn_elGamalGroupEncryptProb hd fun _ _ m₀ m₁ => by
      simp only [elGamalGroupValid, F.isElem_encode, Bool.and_self],
   fun hDDH => DDH.indcpaOn_elGamalGroupEncryptProb hDDH hd⟩

end DecodablePrimeOrderGroupFamily

end Cslib.Crypto
