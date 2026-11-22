/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.GoldwasserMicali
public import CslibFrontier.Probability.DDGTree.Rejection
public import CslibFrontier.Probability.StatisticalDistance.CloseTo
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Probabilistic.RejectionSampling
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Crypto.Game.FourHop
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Foundations.Data.ZMod.CRTUnits
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.RejectionSampling
import CslibFrontier.Probability.Option
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.BindFailure
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.SuppCases
import Mathlib.FieldTheory.Finite.Basic

/-!
# Textbook Goldwasser–Micali `QNR_N^{+1}` key generation and IND-CPA security

Formalizes the strict-PPT textbook Goldwasser–Micali key generator over general distinct odd primes
`p ≠ q` (`ModulusDesc`, without restricting to Blum moduli `p ≡ q ≡ 3 (mod 4)`) and its single-bit
and bitwise multi-bit chosen-plaintext security from `QuadraticResiduosityHard` alone (after
[KatzLindell2020], Section 15.4.4, Construction 15.28 and Theorem 15.29, locator not verified;
pending primary-source verification of [KatzLindell2020] Sections 15.4.3–15.4.4 for registry
enrollment):

* **Per-prime rejection sampling** (`isNonresidueModPrime`, `qnrRejectionSpec`,
  `sampleNonresidueModPrime`): for an odd prime `p`, Euler's criterion tests non-squareness in
  `(ZMod p)ˣ` via `a ^ ((p - 1) / 2) mod p == p - 1` (`isNonresidueModPrime_eq_true_iff`). Because
  `(p - 1) / 2` of the `(p - 1)` units are quadratic nonresidues and `2 ^ (p.size - 1) ≤ p - 1`, a
  single `(encNat p).length`-bit fair-coin block accepts with probability at least `1 / 4` and has
  zero conditional modular bias. Running `3 * (n + 1)` blocks (`sampleNonresidueModPrime`) fails
  with probability at most `(27 / 64) ^ (n + 1) ≤ 1 / 2 ^ (n + 1)` and is uniformly strict PPT.
* **Polynomial-time Fermat-inverse CRT** (`crtCombineNat`, `textbookPublicKey`, `textbookKeyGen`):
  for distinct odd primes `p ≠ q`, `powMod p q (p - 2)` and `powMod q p (q - 2)` invert `q mod p`
  and `p mod q` by Fermat's little theorem without signed extended-GCD arithmetic. Combining
  per-prime nonresidues yields the canonical representative of `(ZMod.unitsChineseRemainder _).symm`
  in `positiveNonresidues p q` (`QNR_N^{+1}`; `crtCombineNat_eq_unitsChineseRemainder_symm_val`,
  `KeyDesc.ofNonresidues`).
* **Statistical closeness and correctness**: for every modulus sampler `gen : ℕ → ProbComp
  ModulusDesc`, `(ProbComp.eval (textbookKeyGen gen n)).map Prod.fst` is within `1 / 2 ^ n`
  statistical distance (`CloseTo`) of the exact uniform law `publicKeyLaw`
  (`closeTo_textbookKeyGen_publicKeyLaw`), decryption succeeds deterministically whenever both
  rejection loops accept (`decrypt_encrypt_of_isNonresidueModPrime`,
  `decryptWord_encryptWord_of_isNonresidueModPrime`), and key generation produces a valid `KeyDesc`
  with probability at least `1 - 1 / 2 ^ n` (`toOuterMeasure_not_exists_keyDesc_textbookKeyGen_le`,
  `closeTo_decrypt_encrypt_textbookKeyGen`, `closeTo_decryptWord_encryptWord_textbookKeyGen`).
* **Single-bit and multi-bit IND-CPA from `QuadraticResiduosityHard` alone**: combining
  `closeTo_textbookKeyGen_publicKeyLaw` with `advantage_publicKeyGame_le_qr` and
  `advantage_publicKeyWordGame_le_qr` proves quantitative bounds with factor-`2` QR loss
  independent of message length (`advantage_textbookGame_le_qr`,
  `advantage_textbookWordGame_le_qr`), single-bit `Encryption.INDCPA`
  (`indcpa_textbookGoldwasserMicali`), and multi-bit `Encryption.WordINDCPA`
  (`wordINDCPA_textbookGoldwasserMicali`) without any Blum-modulus or ideal-key hypothesis.

## Main definitions

* `Cslib.Crypto.GoldwasserMicali.isNonresidueModPrime`: Euler-criterion nonresidue test modulo an
  odd prime.
* `Cslib.Crypto.GoldwasserMicali.qnrRejectionSpec`,
  `Cslib.Crypto.GoldwasserMicali.sampleNonresidueModPrime`: fair-bit block-rejection specification
  and `3 * (n + 1)`-trial strict-PPT nonresidue sampler.
* `Cslib.Crypto.GoldwasserMicali.crtCombineNat`,
  `Cslib.Crypto.GoldwasserMicali.textbookPublicKey`,
  `Cslib.Crypto.GoldwasserMicali.textbookKeyGen`: Fermat-inverse CRT combiner, public-key encoder,
  and textbook Goldwasser–Micali key generator.
* `Cslib.Crypto.GoldwasserMicali.KeyDesc.ofNonresidues`: valid `KeyDesc` constructed from accepted
  per-prime nonresidues.

## Main results

* `Cslib.Crypto.GoldwasserMicali.isNonresidueModPrime_eq_true_iff`: Euler's criterion characterizes
  non-square units modulo an odd prime.
* `Cslib.Crypto.GoldwasserMicali.natCast_crtCombineNat_fst`,
  `Cslib.Crypto.GoldwasserMicali.natCast_crtCombineNat_snd`,
  `Cslib.Crypto.GoldwasserMicali.crtCombineNat_eq_unitsChineseRemainder_symm_val`: residue and
  unit-CRT characterizations of `crtCombineNat`.
* `Cslib.Crypto.GoldwasserMicali.computableInPolyTime_isNonresidueModPrime`,
  `Cslib.Crypto.GoldwasserMicali.computableInPolyTime_crtCombineNat`,
  `Cslib.Crypto.GoldwasserMicali.isPPTOn_sampleNonresidueModPrime`,
  `Cslib.Crypto.GoldwasserMicali.isPPTOn_textbookKeyGen`: polynomial-time and uniform strict-PPT
  certificates.
* `Cslib.Crypto.GoldwasserMicali.decrypt_encrypt_of_isNonresidueModPrime`,
  `Cslib.Crypto.GoldwasserMicali.decryptWord_encryptWord_of_isNonresidueModPrime`,
  `Cslib.Crypto.GoldwasserMicali.toOuterMeasure_not_exists_keyDesc_textbookKeyGen_le`,
  `Cslib.Crypto.GoldwasserMicali.closeTo_decrypt_encrypt_textbookKeyGen`,
  `Cslib.Crypto.GoldwasserMicali.closeTo_decryptWord_encryptWord_textbookKeyGen`: conditional
  deterministic and statistical round-trip decryption correctness.
* `Cslib.Crypto.GoldwasserMicali.closeTo_textbookKeyGen_publicKeyLaw`: `1 / 2 ^ n` statistical
  closeness between `(ProbComp.eval (textbookKeyGen gen n)).map Prod.fst` and `publicKeyLaw`.
* `Cslib.Crypto.GoldwasserMicali.advantage_textbookGame_le_qr`,
  `Cslib.Crypto.GoldwasserMicali.indcpa_textbookGoldwasserMicali`,
  `Cslib.Crypto.GoldwasserMicali.length_textbookPublicKey_le`,
  `Cslib.Crypto.GoldwasserMicali.advantage_textbookWordGame_le_qr`,
  `Cslib.Crypto.GoldwasserMicali.wordINDCPA_textbookGoldwasserMicali`: quantitative bounds and
  asymptotic single-bit and multi-bit IND-CPA security from `QuadraticResiduosityHard` alone.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Section 15.4.4 (Construction 15.28 and Theorem 15.29; locator not verified).
-/

public section

namespace Cslib.Crypto.GoldwasserMicali

open Probability Turing.MultiTapeTM Encryption
open scoped ENNReal NNReal Cslib.Probability.PMF

/-! ### Euler-criterion nonresidue test and capped fair-bit rejection sampler -/

/-- Euler-criterion test for quadratic nonresidues modulo an odd prime `p`: returns `true` when
`0 < a < p` and `a ^ ((p - 1) / 2) mod p = p - 1`. -/
@[expose] def isNonresidueModPrime (p a : ℕ) : Bool :=
  decide (0 < a) && decide (a < p) && (powMod p a ((p - 1) / 2) == p - 1)

/-- Fair-bit block-rejection specification for sampling a quadratic nonresidue modulo `p`: each
trial reads `(encNat p).length` (`= p.size`) fair bits, decodes `BitString.binaryValue`, and
accepts values passing `isNonresidueModPrime p`. -/
def qnrRejectionSpec (p : ℕ) : BlockRejectionSpec ℕ where
  width := (encNat p).length
  attempt w :=
    let a := BitString.binaryValue w
    if isNonresidueModPrime p a then some a else none

/-- Capped strict-PPT sampler for a quadratic nonresidue modulo `p` at security parameter `n`:
run `3 * (n + 1)` independent `(encNat p).length`-bit rejection trials of `qnrRejectionSpec p`,
returning `1` if all trials reject. -/
noncomputable def sampleNonresidueModPrime (n p : ℕ) : ProbComp ℕ :=
  ProbComp.sampleBlockCapped (qnrRejectionSpec p) 1 (3 * (n + 1))

/-- For an odd prime `p`, `isNonresidueModPrime p a` holds iff `a` is the canonical natural
representative of a non-square unit in `(ZMod p)ˣ`. -/
theorem isNonresidueModPrime_eq_true_iff {p : ℕ} [Fact p.Prime] (hp : 2 < p) (a : ℕ) :
    isNonresidueModPrime p a = true ↔
      ∃ u : (ZMod p)ˣ, ¬ IsSquare u ∧ u.val.val = a := by
  have hp_prime : Nat.Prime p := Fact.out
  have hp0 : p ≠ 0 := hp_prime.ne_zero
  have h1p : Fact (1 < p) := ⟨by omega⟩
  have hhalf : (p - 1) / 2 = p / 2 := by
    have := Nat.odd_iff.mp (hp_prime.odd_of_ne_two (by omega))
    omega
  have hodd : p / 2 * 2 = p - 1 := by
    have := Nat.odd_iff.mp (hp_prime.odd_of_ne_two (by omega))
    omega
  have hneg1 : (-1 : ZMod p).val = p - 1 := by
    rw [ZMod.val_neg_of_ne_zero, ZMod.val_one]
  simp only [isNonresidueModPrime, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    powMod_of_ne_zero hp0, hhalf]
  constructor
  · rintro ⟨⟨ha_pos, ha_lt⟩, hpow⟩
    have ha_ne : (a : ZMod p) ≠ 0 := by
      intro h0
      have hval := congrArg ZMod.val h0
      rw [ZMod.val_natCast_of_lt ha_lt, ZMod.val_zero] at hval
      omega
    let u : (ZMod p)ˣ := Units.mk0 (a : ZMod p) ha_ne
    refine ⟨u, ?_, ZMod.val_natCast_of_lt ha_lt⟩
    rintro ⟨r, hu_eq⟩
    have hu1 : u ^ (p / 2) = 1 :=
      (ZMod.euler_criterion_units p u).mp ⟨r, by rw [hu_eq, sq]⟩
    have hcast : ((a ^ (p / 2) % p : ℕ) : ZMod p) = 1 := by
      rw [ZMod.natCast_mod, Nat.cast_pow]
      exact congrArg Units.val hu1
    have hval := congrArg ZMod.val hcast
    rw [ZMod.val_natCast_of_lt (Nat.mod_lt _ (by omega)), ZMod.val_one, hpow] at hval
    omega
  · rintro ⟨u, hnotsq, rfl⟩
    have hu_pos : 0 < u.val.val := Nat.pos_of_ne_zero fun h0 =>
      u.ne_zero ((ZMod.val_eq_zero u.val).mp h0)
    refine ⟨⟨hu_pos, u.val.val_lt⟩, ?_⟩
    have hne1 : u ^ (p / 2) ≠ 1 := by
      intro h1
      obtain ⟨r, hr⟩ := (ZMod.euler_criterion_units p u).mpr h1
      exact hnotsq ⟨r, by rw [← hr, sq]⟩
    have hsq1 : ((u ^ (p / 2) : (ZMod p)ˣ) : ZMod p) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← pow_mul, hodd, ZMod.units_pow_card_sub_one_eq_one,
        Units.val_one]
    have hm1 : ((u ^ (p / 2) : (ZMod p)ˣ) : ZMod p) = -1 := by
      rcases sq_eq_one_iff.mp hsq1 with h1 | hm1
      · exact False.elim (hne1 (Units.ext h1))
      · exact hm1
    have hmod : ((u.val.val ^ (p / 2) % p : ℕ) : ZMod p) = -1 := by
      rw [ZMod.natCast_mod, Nat.cast_pow, ZMod.natCast_zmod_val, ← Units.val_pow_eq_pow_val, hm1]
    have hval := congrArg ZMod.val hmod
    rwa [ZMod.val_natCast_of_lt (Nat.mod_lt _ (by omega)), hneg1] at hval

/-! ### Explicit polynomial-time Fermat-inverse Chinese remaindering -/

/-- Explicit polynomial-time Chinese remainder combination modulo `p * q` via Fermat's little
theorem: for distinct primes `p ≠ q` with `2 < p` and `2 < q`, `powMod p q (p - 2)` and
`powMod q p (q - 2)` invert `q mod p` and `p mod q` without signed extended-GCD arithmetic. -/
@[expose] def crtCombineNat (p q z_p z_q : ℕ) : ℕ :=
  (z_p * q * powMod p q (p - 2) + z_q * p * powMod q p (q - 2)) % (p * q)

/-- Encoded Goldwasser–Micali public key `⟨p * q, crtCombineNat p q z_p z_q⟩` built from prime
factors `(p, q)` and per-prime residues `(z_p, z_q)`. -/
@[expose] def textbookPublicKey (p q z_p z_q : ℕ) : List Bool :=
  encPair encNat encNat (p * q, crtCombineNat p q z_p z_q)

/-- Textbook Goldwasser–Micali key generation (after [KatzLindell2020], Section 15.4.4,
Construction 15.28, locator not verified): draw `d ← gen n`, independently sample `z_p` and `z_q`
via capped fair-bit rejection sampling (`sampleNonresidueModPrime`), and output
`pk = ⟨d.p * d.q, crtCombineNat d.p d.q z_p z_q⟩` and `sk = ⟨d.p, d.q⟩`. -/
noncomputable def textbookKeyGen (gen : ℕ → ProbComp ModulusDesc) (n : ℕ) :
    ProbComp (List Bool × List Bool) := do
  let d ← gen n
  let z_p ← sampleNonresidueModPrime n d.p
  let z_q ← sampleNonresidueModPrime n d.q
  return (textbookPublicKey d.p d.q z_p z_q, encPair encNat encNat (d.p, d.q))

/-- Key pairs in the support of `textbookKeyGen gen n` arise from a supported `ModulusDesc` and
per-prime residues `(z_p, z_q)`. -/
theorem exists_of_mem_support_textbookKeyGen {gen : ℕ → ProbComp ModulusDesc} {n : ℕ}
    {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (textbookKeyGen gen n)).support) :
    ∃ d ∈ (ProbComp.eval (gen n)).support, ∃ z_p z_q : ℕ,
      keys = (textbookPublicKey d.p d.q z_p z_q, encPair encNat encNat (d.p, d.q)) := by
  supp_cases hkeys [textbookKeyGen] with ⟨d, hd, z_p, _, z_q, _, rfl⟩
  exact ⟨d, hd, z_p, z_q, rfl⟩

private theorem crtCombineNat_comm (p q z_p z_q : ℕ) :
    crtCombineNat p q z_p z_q = crtCombineNat q p z_q z_p := by
  simp only [crtCombineNat, add_comm, mul_comm p q]

/-- Modulo `p`, `crtCombineNat p q z_p z_q` reduces to `z_p` for distinct primes `p ≠ q` with
`2 ≤ p`. -/
theorem natCast_crtCombineNat_fst {p q : ℕ} [Fact p.Prime] (hq : Nat.Prime q) (hpq : p ≠ q)
    (hp2 : 2 ≤ p) (z_p z_q : ℕ) :
    ((crtCombineNat p q z_p z_q : ℕ) : ZMod p) = (z_p : ZMod p) := by
  have hp_prime : Nat.Prime p := Fact.out
  unfold crtCombineNat
  rw [← ZMod.natCast_mod (_ % (p * q)) p, Nat.mod_mod_of_dvd _ (dvd_mul_right p q),
    ZMod.natCast_mod, powMod_of_ne_zero hp_prime.ne_zero]
  push_cast
  rw [ZMod.natCast_self, mul_zero, zero_mul, add_zero, ZMod.natCast_mod, Nat.cast_pow, mul_assoc,
    ← pow_succ', show p - 2 + 1 = p - 1 by omega]
  have hq0 : (q : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    rcases (Nat.dvd_prime hq).mp hdvd with rfl | rfl
    · exact hp_prime.ne_one rfl
    · exact hpq rfl
  rw [ZMod.pow_card_sub_one_eq_one hq0, mul_one]

/-- Modulo `q`, `crtCombineNat p q z_p z_q` reduces to `z_q` for distinct primes `p ≠ q` with
`2 ≤ q`. -/
theorem natCast_crtCombineNat_snd {p q : ℕ} [Fact q.Prime] (hp : Nat.Prime p) (hpq : p ≠ q)
    (hq2 : 2 ≤ q) (z_p z_q : ℕ) :
    ((crtCombineNat p q z_p z_q : ℕ) : ZMod q) = (z_q : ZMod q) := by
  rw [crtCombineNat_comm]
  exact natCast_crtCombineNat_fst hp hpq.symm hq2 z_q z_p

/-- On canonical natural representatives of `(u_p, u_q) : (ZMod d.p)ˣ × (ZMod d.q)ˣ`,
`crtCombineNat d.p d.q` computes the canonical natural representative of
`(ZMod.unitsChineseRemainder hcop).symm (u_p, u_q)`. -/
theorem crtCombineNat_eq_unitsChineseRemainder_symm_val (d : ModulusDesc)
    (hcop : d.p.Coprime d.q) (u_p : (ZMod d.p)ˣ) (u_q : (ZMod d.q)ˣ) :
    crtCombineNat d.p d.q u_p.val.val u_q.val.val =
      ((ZMod.unitsChineseRemainder hcop).symm (u_p, u_q)).val.val := by
  let u := (ZMod.unitsChineseRemainder hcop).symm (u_p, u_q)
  have hlt : crtCombineNat d.p d.q u_p.val.val u_q.val.val < d.p * d.q :=
    Nat.mod_lt _ (Nat.mul_pos d.prime_p.pos d.prime_q.pos)
  rw [← ZMod.val_natCast_of_lt hlt]
  refine congrArg ZMod.val ((ZMod.chineseRemainder hcop).injective ?_)
  rw [map_natCast]
  have hu : ZMod.unitsChineseRemainder hcop u = (u_p, u_q) :=
    (ZMod.unitsChineseRemainder hcop).apply_symm_apply (u_p, u_q)
  have h1 : (ZMod.chineseRemainder hcop u.val).1 = u_p.val := by
    rw [← ZMod.coe_unitsChineseRemainder_fst hcop u, hu]
  have h2 : (ZMod.chineseRemainder hcop u.val).2 = u_q.val := by
    rw [← ZMod.coe_unitsChineseRemainder_snd hcop u, hu]
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_natCast, natCast_crtCombineNat_fst d.prime_q d.ne_pq d.two_lt_p.le,
      ZMod.natCast_zmod_val, h1]
  · rw [Prod.snd_natCast, natCast_crtCombineNat_snd d.prime_p d.ne_pq d.two_lt_q.le,
      ZMod.natCast_zmod_val, h2]

/-- Construct a valid `KeyDesc` (`z ∈ QNR_N^{+1}`) from `d : ModulusDesc` and any pair `(z_p, z_q)`
passing `isNonresidueModPrime`. -/
def KeyDesc.ofNonresidues (d : ModulusDesc) {z_p z_q : ℕ}
    (hp : isNonresidueModPrime d.p z_p = true) (hq : isNonresidueModPrime d.q z_q = true) :
    KeyDesc where
  toModulusDesc := d
  z := crtCombineNat d.p d.q z_p z_q
  exists_posNonresidue := by
    obtain ⟨u_p, hnsq_p, rfl⟩ := (isNonresidueModPrime_eq_true_iff d.two_lt_p z_p).mp hp
    obtain ⟨u_q, hnsq_q, rfl⟩ := (isNonresidueModPrime_eq_true_iff d.two_lt_q z_q).mp hq
    have hcop : d.p.Coprime d.q := (Nat.coprime_primes d.prime_p d.prime_q).mpr d.ne_pq
    let u := (ZMod.unitsChineseRemainder hcop).symm (u_p, u_q)
    refine ⟨u, ?_, (crtCombineNat_eq_unitsChineseRemainder_symm_val d hcop u_p u_q).symm⟩
    rw [mem_positiveNonresidues_iff_unitsChineseRemainder d.p d.q hcop d.two_lt_p d.two_lt_q u,
      (ZMod.unitsChineseRemainder hcop).apply_symm_apply]
    exact ⟨hnsq_p, hnsq_q⟩

/-! ### Polynomial-time and uniform strict-PPT certificates -/

/-- `isNonresidueModPrime` is computable in polynomial time on binary naturals. -/
theorem computableInPolyTime_isNonresidueModPrime {α : Type} {input : α ↪ List Bool}
    {p a : α → ℕ} (hp : ComputableInPolyTime p input encNat)
    (ha : ComputableInPolyTime a input encNat) :
    ComputableInPolyTime (fun x => isNonresidueModPrime (p x) (a x)) input encBool := by
  have hexp : ComputableInPolyTime (fun x => (p x - 1) / 2) input encNat :=
    .binary_div' (.binary_sub' hp (.const 1)) (.const 2)
  have hpm1 : ComputableInPolyTime (fun x => p x - 1) input encNat :=
    .binary_sub' hp (.const 1)
  have hpos := ComputableInPolyTime.binary_lt' (.const 0) ha
  have hlt := ComputableInPolyTime.binary_lt' ha hp
  have heq := (computableInPolyTime_powMod hp ha hexp).beq hpm1
  unfold isNonresidueModPrime
  exact ComputableInPolyTime.bool_and.comp
    ((ComputableInPolyTime.bool_and.comp (hpos.prod hlt)).prod heq)

/-- `crtCombineNat` is computable in polynomial time on binary naturals. -/
theorem computableInPolyTime_crtCombineNat {α : Type} {input : α ↪ List Bool}
    {p q z_p z_q : α → ℕ} (hp : ComputableInPolyTime p input encNat)
    (hq : ComputableInPolyTime q input encNat)
    (hzp : ComputableInPolyTime z_p input encNat)
    (hzq : ComputableInPolyTime z_q input encNat) :
    ComputableInPolyTime (fun x => crtCombineNat (p x) (q x) (z_p x) (z_q x)) input encNat := by
  have hN := ComputableInPolyTime.binary_mul' hp hq
  have hinv_q := computableInPolyTime_powMod hp hq (.binary_sub' hp (.const 2))
  have hinv_p := computableInPolyTime_powMod hq hp (.binary_sub' hq (.const 2))
  have hterm1 := ComputableInPolyTime.binary_mul' (.binary_mul' hzp hq) hinv_q
  have hterm2 := ComputableInPolyTime.binary_mul' (.binary_mul' hzq hp) hinv_p
  unfold crtCombineNat
  exact .binary_mod' (.binary_add' hterm1 hterm2) hN

/-- `sampleNonresidueModPrime` is uniformly strict PPT for a unary security parameter and binary
modulus. -/
theorem isPPTOn_sampleNonresidueModPrime {α : Type} {input : α ↪ List Bool}
    {n p : α → ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hp : ComputableInPolyTime p input encNat) :
    IsPPTOn input encNat (fun x => sampleNonresidueModPrime (n x) (p x)) := by
  have htrials : ComputableInPolyTime (fun x => 3 * (n x + 1)) input encUnary := by fun_prop
  have hwidth : ComputableInPolyTime (fun x => (qnrRejectionSpec (p x)).width) input encUnary :=
    (ComputableInPolyTime.encoding_length encNat).comp hp
  have ha : ComputableInPolyTime (fun pair : α × List Bool => BitString.binaryValue pair.2)
      (encPair input encBits) encNat :=
    ComputableInPolyTime.bitsBinaryValue.comp (ComputableInPolyTime.snd input encBits)
  have hp1 := hp.comp (ComputableInPolyTime.fst input encBits)
  have hcond := computableInPolyTime_isNonresidueModPrime hp1 ha
  have hyes : ComputableInPolyTime
      (fun pair : α × List Bool => (some (BitString.binaryValue pair.2) : Option ℕ))
      (encPair input encBits) (encOption encNat) :=
    (ComputableInPolyTime.optionSome encNat).comp ha
  have hattempt : ComputableInPolyTime
      (fun pair : α × List Bool => (qnrRejectionSpec (p pair.1)).attempt pair.2)
      (encPair input encBits) (encOption encNat) :=
    ComputableInPolyTime.ite hcond hyes (.const none)
  exact isPPTOn_sampleBlockCapped htrials hwidth hattempt (.const 1)

/-- `textbookKeyGen gen` is uniformly strict PPT whenever the modulus sampler `gen` is. -/
theorem isPPTOn_textbookKeyGen {gen : ℕ → ProbComp ModulusDesc}
    (hgen : IsPPTOn encUnary encModulusDesc gen) :
    IsPPTOn encUnary (encPair encBits encBits) (textbookKeyGen gen) := by
  let E₁ := encPair encUnary encModulusDesc
  let E₂ := encPair E₁ encNat
  let E₃ := encPair E₂ encNat
  have hn₁ := ComputableInPolyTime.fst encUnary encModulusDesc
  have hd₁ := (ComputableInPolyTime.of_eq (f := ModulusDesc.toPair)
    (encIn := encModulusDesc) (encOut := encPair encNat encNat) fun _ => rfl).comp
    (ComputableInPolyTime.snd encUnary encModulusDesc)
  have hp₁ := hd₁.fst'
  have hq₁ := hd₁.snd'
  have hzp_prog : IsPPTOn E₁ encNat (fun x : ℕ × ModulusDesc =>
      sampleNonresidueModPrime x.1 x.2.p) :=
    isPPTOn_sampleNonresidueModPrime hn₁ hp₁
  have hf₂ := ComputableInPolyTime.fst E₁ encNat
  have hzq_prog : IsPPTOn E₂ encNat (fun y : (ℕ × ModulusDesc) × ℕ =>
      sampleNonresidueModPrime y.1.1 y.1.2.q) :=
    isPPTOn_sampleNonresidueModPrime (hn₁.comp hf₂) (hq₁.comp hf₂)
  have hf₃ := ComputableInPolyTime.fst E₂ encNat
  have hp₃ := (hp₁.comp hf₂).comp hf₃
  have hq₃ := (hq₁.comp hf₂).comp hf₃
  have hzp₃ := (ComputableInPolyTime.snd E₁ encNat).comp hf₃
  have hzq₃ := ComputableInPolyTime.snd E₂ encNat
  have hN₃ := ComputableInPolyTime.binary_mul' hp₃ hq₃
  have hcrt₃ := computableInPolyTime_crtCombineNat hp₃ hq₃ hzp₃ hzq₃
  have hpk₃ : ComputableInPolyTime
      (fun w : ((ℕ × ModulusDesc) × ℕ) × ℕ =>
        textbookPublicKey w.1.1.2.p w.1.1.2.q w.1.2 w.2) E₃ encBits :=
    (hN₃.prod hcrt₃).encoding_comp
  have hsk₃ : ComputableInPolyTime
      (fun w : ((ℕ × ModulusDesc) × ℕ) × ℕ =>
        encPair encNat encNat (w.1.1.2.p, w.1.1.2.q)) E₃ encBits :=
    (hp₃.prod hq₃).encoding_comp
  unfold textbookKeyGen
  exact IsPPTOn.bind_with hgen
    (IsPPTOn.bind_with hzp_prog (IsPPTOn.bind_with hzq_prog (hpk₃.prod hsk₃).isPPTOn))

/-! ### Rejection-sampling law, `1 / 2 ^ n` closeness to `publicKeyLaw`, and correctness -/

open Classical in
private def primeNonresidues (p : ℕ) [NeZero p] : Finset (ZMod p)ˣ :=
  Finset.univ.filter fun u => ¬ IsSquare u

private theorem mem_primeNonresidues {p : ℕ} [NeZero p] {u : (ZMod p)ˣ} :
    u ∈ primeNonresidues p ↔ ¬ IsSquare u := by
  classical
  simp [primeNonresidues]

private theorem two_mul_card_primeNonresidues {p : ℕ} [Fact p.Prime] (hp : 2 < p) :
    2 * (primeNonresidues p).card = p - 1 := by
  have hp_prime : Nat.Prime p := Fact.out
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hp_prime]
  rw [primeNonresidues, ZMod.card_nonsquares_units p hp, ZMod.two_mul_card_squares_units p hp,
    hcard]

private theorem card_primeNonresidues {p : ℕ} [Fact p.Prime] (hp : 2 < p) :
    (primeNonresidues p).card = (p - 1) / 2 := by
  have h := two_mul_card_primeNonresidues hp
  omega

private theorem primeNonresidues_nonempty {p : ℕ} [Fact p.Prime] (hp : 2 < p) :
    (primeNonresidues p).Nonempty := by
  rw [← Finset.card_pos, card_primeNonresidues hp]
  omega

private noncomputable def primeNonresidueLaw (p : ℕ) [Fact p.Prime] (hp : 2 < p) : PMF ℕ :=
  letI : Nonempty (primeNonresidues p) := (primeNonresidues_nonempty hp).to_subtype
  (PMF.uniformOfFintype (primeNonresidues p)).map fun u => u.1.val.val

private theorem singleLaw_qnrRejectionSpec_some_raw (p a : ℕ) :
    (qnrRejectionSpec p).singleLaw (some a) =
      if isNonresidueModPrime p a then ((2 ^ p.size : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
  let g : ℕ → Option ℕ := fun v => if isNonresidueModPrime p v then some v else none
  have hmap : (qnrRejectionSpec p).singleLaw =
      ((PMF.uniformOfFintype (Fin (2 ^ p.size))).map Fin.val).map g := by
    calc
      (qnrRejectionSpec p).singleLaw =
          (BitString.uniformList p.size).map (g ∘ BitString.binaryValue) := by
        simp only [BlockRejectionSpec.singleLaw, qnrRejectionSpec, encNat_apply,
          ← Nat.size_eq_bits_len, g, Function.comp_def]
      _ = ((BitString.uniformList p.size).map BitString.binaryValue).map g :=
        (PMF.map_comp _ _ _).symm
      _ = ((PMF.uniformOfFintype (Fin (2 ^ p.size))).map Fin.val).map g := by
        rw [BitString.uniformList_binaryValue]
  rw [hmap, PMF.map_comp, PMF.map_apply, tsum_fintype]
  split_ifs with ha
  · have ha_lt : a < p := by
      simp only [isNonresidueModPrime, Bool.and_eq_true, decide_eq_true_eq] at ha
      exact ha.1.2
    have ha_pow : a < 2 ^ p.size := lt_trans ha_lt (Nat.lt_size_self p)
    rw [Finset.sum_eq_single ⟨a, ha_pow⟩]
    · simp [g, ha, PMF.uniformOfFintype_apply]
    · intro j _ hj
      simp only [Function.comp_apply, g]
      by_cases hj_nr : isNonresidueModPrime p j.val
      · simp only [hj_nr, ↓reduceIte, Option.some.injEq]
        split_ifs with heq
        · exfalso
          apply hj
          ext
          exact heq.symm
        · rfl
      · simp [hj_nr]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  · refine Finset.sum_eq_zero fun j _ => ?_
    simp only [Function.comp_apply, g]
    by_cases hj_nr : isNonresidueModPrime p j.val
    · simp only [hj_nr, ↓reduceIte, Option.some.injEq]
      split_ifs with heq
      · exfalso
        exact ha (heq ▸ hj_nr)
      · rfl
    · simp [hj_nr]

private theorem primeNonresidueLaw_apply {p : ℕ} [Fact p.Prime] (hp : 2 < p) (a : ℕ) :
    primeNonresidueLaw p hp a =
      if isNonresidueModPrime p a then ((primeNonresidues p).card : ℝ≥0∞)⁻¹ else 0 := by
  classical
  have : Nonempty (primeNonresidues p) := (primeNonresidues_nonempty hp).to_subtype
  rw [primeNonresidueLaw, PMF.map_apply, tsum_fintype]
  split_ifs with ha
  · obtain ⟨u, hu, rfl⟩ := (isNonresidueModPrime_eq_true_iff hp a).mp ha
    have hu_mem : u ∈ primeNonresidues p := mem_primeNonresidues.mpr hu
    rw [Finset.sum_eq_single ⟨u, hu_mem⟩]
    · simp [PMF.uniformOfFintype_apply, Fintype.card_coe]
    · intro v _ hv
      simp only [PMF.uniformOfFintype_apply, Fintype.card_coe]
      split_ifs with heq
      · exfalso
        apply hv
        ext
        rw [← ZMod.natCast_zmod_val u.val, ← ZMod.natCast_zmod_val v.1.val, heq]
      · rfl
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  · refine Finset.sum_eq_zero fun v _ => ?_
    split_ifs with heq
    · exfalso
      subst heq
      have hmem := mem_primeNonresidues.mp v.2
      exact ha ((isNonresidueModPrime_eq_true_iff hp _).mpr ⟨v.1, hmem, rfl⟩)
    · rfl

private theorem acceptProb_qnrRejectionSpec {p : ℕ} [Fact p.Prime] (hp : 2 < p) :
    (qnrRejectionSpec p).acceptProb =
      ((primeNonresidues p).card : ℝ≥0∞) / ((2 ^ p.size : ℕ) : ℝ≥0∞) := by
  classical
  have hsum : ∑' a, (qnrRejectionSpec p).singleLaw (some a) =
      ((primeNonresidues p).card : ℝ≥0∞) / ((2 ^ p.size : ℕ) : ℝ≥0∞) := by
    let img := (primeNonresidues p).image (fun u : (ZMod p)ˣ => u.val.val)
    have hinj : Set.InjOn (fun u : (ZMod p)ˣ => u.val.val) (primeNonresidues p) := by
      intro u _ v _ huv
      dsimp only at huv
      ext
      rw [← ZMod.natCast_zmod_val u.val, ← ZMod.natCast_zmod_val v.val, huv]
    rw [tsum_eq_sum (s := img)]
    · trans (∑ _a ∈ img, ((2 ^ p.size : ℕ) : ℝ≥0∞)⁻¹)
      · refine Finset.sum_congr rfl fun a ha => ?_
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
        have hnr : isNonresidueModPrime p u.val.val = true :=
          (isNonresidueModPrime_eq_true_iff hp _).mpr ⟨u, mem_primeNonresidues.mp hu, rfl⟩
        rw [singleLaw_qnrRejectionSpec_some_raw p, ite_eq_left hnr]
      · rw [Finset.sum_const, Finset.card_image_of_injOn hinj, nsmul_eq_mul, div_eq_mul_inv]
    · intro a ha
      rw [singleLaw_qnrRejectionSpec_some_raw p]
      split_ifs with hnr
      · exfalso
        obtain ⟨u, hu, rfl⟩ := (isNonresidueModPrime_eq_true_iff hp a).mp hnr
        exact ha (Finset.mem_image.mpr ⟨u, mem_primeNonresidues.mpr hu, rfl⟩)
      · rfl
  have htotal := (qnrRejectionSpec p).singleLaw.tsum_coe
  rw [Probability.tsum_option_eq, add_comm] at htotal
  have hacc := (ENNReal.eq_sub_of_add_eq (qnrRejectionSpec p).rejectProb_ne_top htotal).symm
  exact hacc.trans hsum

private theorem singleLaw_qnrRejectionSpec_some {p : ℕ} [Fact p.Prime] (hp : 2 < p) (a : ℕ) :
    (qnrRejectionSpec p).singleLaw (some a) =
      (qnrRejectionSpec p).acceptProb * primeNonresidueLaw p hp a := by
  rw [singleLaw_qnrRejectionSpec_some_raw p, acceptProb_qnrRejectionSpec hp,
    primeNonresidueLaw_apply hp]
  split_ifs with ha
  · have hne : ((primeNonresidues p).card : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.mpr (primeNonresidues_nonempty hp).card_ne_zero
    rw [div_eq_mul_inv, mul_right_comm, ENNReal.mul_inv_cancel hne (ENNReal.natCast_ne_top _),
      one_mul]
  · rw [mul_zero]

private theorem rejectProb_qnrRejectionSpec_le {p : ℕ} [Fact p.Prime] (hp : 2 < p) :
    (qnrRejectionSpec p).rejectProb ≤ ((3 / 4 : ℝ≥0) : ℝ≥0∞) := by
  have hsize_ge : 2 ≤ p.size := Nat.lt_size.mpr (by omega : 2 ^ 1 ≤ p)
  have hpow_le_p : 2 ^ (p.size - 1) ≤ p := Nat.lt_size.mp (by omega : p.size - 1 < p.size)
  have hpow_ne_p : 2 ^ (p.size - 1) ≠ p := by
    intro heq
    have hdvd : 2 ∣ 2 ^ (p.size - 1) := dvd_pow_self 2 (by omega)
    rw [heq] at hdvd
    rcases (Nat.dvd_prime Fact.out).mp hdvd with h2 | h2 <;> omega
  have hpow_le_sub : 2 ^ (p.size - 1) ≤ p - 1 := by omega
  have htwo_card := two_mul_card_primeNonresidues hp
  have hfour : 2 ^ p.size ≤ 4 * (primeNonresidues p).card := by
    have hsplit : 2 ^ p.size = 2 * 2 ^ (p.size - 1) := by
      conv_lhs => rw [show p.size = (p.size - 1) + 1 by omega, pow_succ']
    omega
  have hquarter_coe : ((1 / 4 : ℝ≥0) : ℝ≥0∞) = 1 / 4 := by
    rw [ENNReal.coe_div (by norm_num), ENNReal.coe_one, ENNReal.coe_ofNat]
  have hacc : ((1 / 4 : ℝ≥0) : ℝ≥0∞) ≤ (qnrRejectionSpec p).acceptProb := by
    rw [hquarter_coe, acceptProb_qnrRejectionSpec hp,
      ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (ENNReal.natCast_ne_top _))]
    calc
      (1 / 4 : ℝ≥0∞) * ((2 ^ p.size : ℕ) : ℝ≥0∞)
        ≤ (1 / 4 : ℝ≥0∞) * ((4 * (primeNonresidues p).card : ℕ) : ℝ≥0∞) := by gcongr
      _ = ((primeNonresidues p).card : ℝ≥0∞) := by
        rw [Nat.cast_mul, Nat.cast_ofNat, ← mul_assoc, one_div,
          ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  have hsub_nn : ((1 : ℝ≥0) - (1 / 4 : ℝ≥0)) = (3 / 4 : ℝ≥0) :=
    NNReal.eq (by
      have hle : (1 / 4 : ℝ≥0) ≤ 1 := by rw [← NNReal.coe_le_coe]; push_cast; norm_num
      rw [NNReal.coe_sub hle]; push_cast; norm_num)
  calc
    (qnrRejectionSpec p).rejectProb
      = 1 - (qnrRejectionSpec p).acceptProb :=
        (ENNReal.sub_sub_cancel ENNReal.one_ne_top (qnrRejectionSpec p).rejectProb_le_one).symm
    _ ≤ ((1 : ℝ≥0) : ℝ≥0∞) - ((1 / 4 : ℝ≥0) : ℝ≥0∞) := tsub_le_tsub_left hacc 1
    _ = ((3 / 4 : ℝ≥0) : ℝ≥0∞) := by rw [← ENNReal.coe_sub, hsub_nn]

private theorem rejectProb_pow_three_mul_le {p : ℕ} [Fact p.Prime] (hp : 2 < p) (n : ℕ) :
    (qnrRejectionSpec p).rejectProb ^ (3 * (n + 1)) ≤ ((1 / 2 ^ (n + 1) : ℝ≥0) : ℝ≥0∞) := by
  have hcube : ((3 / 4 : ℝ≥0) : ℝ≥0∞) ^ 3 ≤ ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.coe_pow]
    exact ENNReal.coe_le_coe.mpr (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  calc
    (qnrRejectionSpec p).rejectProb ^ (3 * (n + 1))
      ≤ ((3 / 4 : ℝ≥0) : ℝ≥0∞) ^ (3 * (n + 1)) :=
        pow_le_pow_left' (rejectProb_qnrRejectionSpec_le hp) _
    _ = (((3 / 4 : ℝ≥0) : ℝ≥0∞) ^ 3) ^ (n + 1) := pow_mul _ 3 (n + 1)
    _ ≤ ((1 / 2 : ℝ≥0) : ℝ≥0∞) ^ (n + 1) := pow_le_pow_left' hcube (n + 1)
    _ = ((1 / 2 ^ (n + 1) : ℝ≥0) : ℝ≥0∞) := by
        rw [← ENNReal.coe_pow, one_div_pow]

private theorem closeTo_runCapped {α : Type} {spec : BlockRejectionSpec α} {target : PMF α}
    (h : ∀ a, spec.singleLaw (some a) = spec.acceptProb * target a)
    (fallback : α) (t : ℕ) :
    CloseTo (spec.runCapped fallback t) target (spec.rejectProb ^ t) := by
  set r := spec.rejectProb ^ t
  have hr1 : r ≤ 1 := pow_le_one₀ zero_le spec.rejectProb_le_one
  have hpt (a : α) : (1 - r) * target a ≤ spec.runCapped fallback t a := by
    rw [← spec.runTrials_some_of_singleLaw h t a, BlockRejectionSpec.runCapped, PMF.map_apply]
    refine le_trans ?_ (le_tsum _ (some a))
    simp
  refine CloseTo.symm fun E => ?_
  have hdom : (1 - r) * target.toOuterMeasure E ≤ (spec.runCapped fallback t).toOuterMeasure E := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
    refine tsum_le_tsum fun a => ?_
    by_cases ha : a ∈ E
    · simp only [Set.indicator_of_mem ha]
      exact hpt a
    · simp [Set.indicator_of_notMem ha]
  calc
    target.toOuterMeasure E
      = (1 - r) * target.toOuterMeasure E + r * target.toOuterMeasure E := by
        rw [← add_mul, tsub_add_cancel_of_le hr1, one_mul]
    _ ≤ (spec.runCapped fallback t).toOuterMeasure E + r :=
        add_le_add hdom (mul_le_of_le_one_right zero_le (PMF.toOuterMeasure_le_one target E))

private theorem closeTo_sampleNonresidueModPrime {p : ℕ} [Fact p.Prime] (hp : 2 < p) (n : ℕ) :
    CloseTo (ProbComp.eval (sampleNonresidueModPrime n p)) (primeNonresidueLaw p hp)
      ((1 / 2 ^ (n + 1) : ℝ≥0) : ℝ≥0∞) := by
  rw [sampleNonresidueModPrime, ProbComp.eval_sampleBlockCapped]
  exact (closeTo_runCapped (singleLaw_qnrRejectionSpec_some hp) 1 (3 * (n + 1))).mono
    (rejectProb_pow_three_mul_le hp n)

private theorem toOuterMeasure_not_isNonresidueModPrime_le {p : ℕ} [Fact p.Prime] (hp : 2 < p)
    (n : ℕ) :
    (ProbComp.eval (sampleNonresidueModPrime n p)).toOuterMeasure
      {a | isNonresidueModPrime p a = false} ≤ ((1 / 2 ^ (n + 1) : ℝ≥0) : ℝ≥0∞) := by
  have hclose := closeTo_sampleNonresidueModPrime hp n {a | isNonresidueModPrime p a = false}
  have htarget0 : (primeNonresidueLaw p hp).toOuterMeasure
      {a | isNonresidueModPrime p a = false} = 0 := by
    rw [PMF.toOuterMeasure_apply, tsum_eq_zero_iff]
    intro a
    simp [Set.indicator, primeNonresidueLaw_apply hp]
  simpa only [htarget0, zero_add] using hclose

private theorem one_div_two_pow_succ_add (n : ℕ) :
    ((1 / 2 ^ (n + 1) : ℝ≥0) : ℝ≥0∞) + ((1 / 2 ^ (n + 1) : ℝ≥0) : ℝ≥0∞) =
      ((1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) := by
  rw [← ENNReal.coe_add]
  congr 1
  rw [pow_succ]; ring

/-- Statistical closeness of `textbookKeyGen gen` to `publicKeyLaw` (after [KatzLindell2020],
Section 15.4.4, Construction 15.28, locator not verified): for any modulus sampler
`gen : ℕ → ProbComp ModulusDesc` (without any Blum or bit-length hypothesis), the public-key
marginal of `textbookKeyGen gen n` is within `1 / 2 ^ n` statistical distance (`CloseTo`) of the
exact uniform `QNR_N^{+1}` law `publicKeyLaw (fun k => ProbComp.eval (gen k)) n`. -/
theorem closeTo_textbookKeyGen_publicKeyLaw (gen : ℕ → ProbComp ModulusDesc) (n : ℕ) :
    CloseTo ((ProbComp.eval (textbookKeyGen gen n)).map Prod.fst)
      (publicKeyLaw (fun k => ProbComp.eval (gen k)) n) ((1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) := by
  have hperModulus (d : ModulusDesc) :
      CloseTo
        ((ProbComp.eval (sampleNonresidueModPrime n d.p)).bind fun z_p =>
          (ProbComp.eval (sampleNonresidueModPrime n d.q)).map fun z_q =>
            textbookPublicKey d.p d.q z_p z_q)
        ((PMF.uniformOfFintype (positiveNonresidues d.p d.q)).map fun z =>
          encPair encNat encNat (d.p * d.q, z.1.val.val))
        ((1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) := by
    have : Nonempty (primeNonresidues d.p) := (primeNonresidues_nonempty d.two_lt_p).to_subtype
    have : Nonempty (primeNonresidues d.q) := (primeNonresidues_nonempty d.two_lt_q).to_subtype
    have hcop : d.p.Coprime d.q := (Nat.coprime_primes d.prime_p d.prime_q).mpr d.ne_pq
    let e : primeNonresidues d.p × primeNonresidues d.q ≃ positiveNonresidues d.p d.q :=
      { toFun := fun pq =>
          ⟨(ZMod.unitsChineseRemainder hcop).symm (pq.1.1, pq.2.1), by
            rw [mem_positiveNonresidues_iff_unitsChineseRemainder d.p d.q hcop
                d.two_lt_p d.two_lt_q,
              (ZMod.unitsChineseRemainder hcop).apply_symm_apply]
            exact ⟨mem_primeNonresidues.mp pq.1.2, mem_primeNonresidues.mp pq.2.2⟩⟩
        invFun := fun u =>
          have hu := (mem_positiveNonresidues_iff_unitsChineseRemainder d.p d.q hcop
            d.two_lt_p d.two_lt_q u.1).mp u.2
          (⟨(ZMod.unitsChineseRemainder hcop u.1).1, mem_primeNonresidues.mpr hu.1⟩,
           ⟨(ZMod.unitsChineseRemainder hcop u.1).2, mem_primeNonresidues.mpr hu.2⟩)
        left_inv := fun ⟨⟨u_p, hp_mem⟩, ⟨u_q, hq_mem⟩⟩ => by
          ext <;> simp [(ZMod.unitsChineseRemainder hcop).apply_symm_apply]
        right_inv := fun ⟨u, hu_mem⟩ => by
          ext
          exact congrArg Units.val ((ZMod.unitsChineseRemainder hcop).symm_apply_apply u) }
    have hideal_eq :
        ((primeNonresidueLaw d.p d.two_lt_p).bind fun z_p =>
          (primeNonresidueLaw d.q d.two_lt_q).map fun z_q =>
            textbookPublicKey d.p d.q z_p z_q) =
        ((PMF.uniformOfFintype (positiveNonresidues d.p d.q)).map fun z =>
          encPair encNat encNat (d.p * d.q, z.1.val.val)) := by
      simp only [primeNonresidueLaw, PMF.bind_map, PMF.map_comp, Function.comp_def,
        textbookPublicKey]
      have hbody :
          (fun u_p : primeNonresidues d.p =>
            (PMF.uniformOfFintype (primeNonresidues d.q)).map fun u_q : primeNonresidues d.q =>
              encPair encNat encNat
                (d.p * d.q, crtCombineNat d.p d.q u_p.1.val.val u_q.1.val.val)) =
          (fun u_p : primeNonresidues d.p =>
            (PMF.uniformOfFintype (primeNonresidues d.q)).bind fun u_q : primeNonresidues d.q =>
              PMF.pure (encPair encNat encNat (d.p * d.q, (e (u_p, u_q)).1.val.val))) := by
        funext u_p
        rw [PMF.map]
        congr 1; funext u_q
        rw [Function.comp_apply,
          crtCombineNat_eq_unitsChineseRemainder_symm_val d hcop u_p.1 u_q.1]
        rfl
      rw [hbody, Probability.PMF.uniformOfFintype_bind_bind_equiv e
        (fun z => PMF.pure (encPair encNat encNat (d.p * d.q, z.1.val.val)))]
      rfl
    rw [← hideal_eq, ← one_div_two_pow_succ_add n]
    exact CloseTo.bind (closeTo_sampleNonresidueModPrime d.two_lt_p n) fun z_p _ =>
      (closeTo_sampleNonresidueModPrime d.two_lt_q n).map _
  have hrew : (ProbComp.eval (textbookKeyGen gen n)).map Prod.fst =
      (ProbComp.eval (gen n)).bind fun d =>
        (ProbComp.eval (sampleNonresidueModPrime n d.p)).bind fun z_p =>
          (ProbComp.eval (sampleNonresidueModPrime n d.q)).map fun z_q =>
            textbookPublicKey d.p d.q z_p z_q := by
    simp only [textbookKeyGen, pmf_norm, PMF.map, Function.comp_def]
  have hpub : publicKeyLaw (fun k => ProbComp.eval (gen k)) n =
      (ProbComp.eval (gen n)).bind fun d =>
        (PMF.uniformOfFintype (positiveNonresidues d.p d.q)).map fun z =>
          encPair encNat encNat (d.p * d.q, z.1.val.val) := rfl
  rw [hrew, hpub]
  exact CloseTo.bind_right (ProbComp.eval (gen n)) fun d _ => hperModulus d

/-! ### Conditional deterministic and statistical decryption correctness -/

/-- Deterministic conditional correctness for 1-bit encryption: whenever `z_p` and `z_q` satisfy
`isNonresidueModPrime` for `d : ModulusDesc`, every supported ciphertext of `encrypt` under
`textbookPublicKey d.p d.q z_p z_q` decrypts to `m`. -/
theorem decrypt_encrypt_of_isNonresidueModPrime (d : ModulusDesc) {z_p z_q n : ℕ}
    (hp : isNonresidueModPrime d.p z_p = true) (hq : isNonresidueModPrime d.q z_q = true)
    (m : Bool) {ct : List Bool}
    (hct : ct ∈ (ProbComp.eval (encrypt n (textbookPublicKey d.p d.q z_p z_q) m)).support) :
    decrypt (encPair encNat encNat (d.p, d.q)) ct = m := by
  let k := KeyDesc.ofNonresidues d hp hq
  have hpk : textbookPublicKey d.p d.q z_p z_q = encPair encNat encNat (k.modulus, k.z) := rfl
  have hsk : encPair encNat encNat (d.p, d.q) = encPair encNat encNat (k.p, k.q) := rfl
  rw [hpk] at hct
  rw [hsk]
  exact k.decrypt_encrypt m hct

/-- Deterministic conditional correctness for bitwise multi-bit encryption: whenever `z_p` and
`z_q` satisfy `isNonresidueModPrime` for `d : ModulusDesc`, every supported ciphertext of
`encryptWord` under `textbookPublicKey d.p d.q z_p z_q` decrypts to `bits`. -/
theorem decryptWord_encryptWord_of_isNonresidueModPrime (d : ModulusDesc) {z_p z_q n : ℕ}
    (hp : isNonresidueModPrime d.p z_p = true) (hq : isNonresidueModPrime d.q z_q = true)
    (bits : List Bool) {ct : List Bool}
    (hct : ct ∈ (ProbComp.eval (encryptWord n (textbookPublicKey d.p d.q z_p z_q) bits)).support) :
    decryptWord (encPair encNat encNat (d.p, d.q)) ct = bits :=
  Encryption.bitwiseDecrypt_bitwiseEncrypt
    (fun b _ h => decrypt_encrypt_of_isNonresidueModPrime d hp hq b h) bits hct

/-- Over `keys ← textbookKeyGen gen n`, the probability that `keys` fails to arise from a valid
`KeyDesc` (`z ∈ QNR_N^{+1}`) is at most `1 / 2 ^ n`. Outside that `1 / 2 ^ n` rejection tail, every
1-bit and multi-bit encryption under `keys.1` decrypts deterministically with zero error under
`keys.2`. -/
theorem toOuterMeasure_not_exists_keyDesc_textbookKeyGen_le
    (gen : ℕ → ProbComp ModulusDesc) (n : ℕ) :
    (ProbComp.eval (textbookKeyGen gen n)).toOuterMeasure
      {keys | ¬ ∃ k : KeyDesc,
        keys = (encPair encNat encNat (k.modulus, k.z), encPair encNat encNat (k.p, k.q))} ≤
      ((1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) := by
  let bad : Set (List Bool × List Bool) :=
    {keys | ¬ ∃ k : KeyDesc,
      keys = (encPair encNat encNat (k.modulus, k.z), encPair encNat encNat (k.p, k.q))}
  have hper (d : ModulusDesc) :
      (((ProbComp.eval (sampleNonresidueModPrime n d.p)).bind fun z_p =>
        (ProbComp.eval (sampleNonresidueModPrime n d.q)).bind fun z_q =>
          PMF.pure (textbookPublicKey d.p d.q z_p z_q, encPair encNat encNat (d.p, d.q)))
        ).toOuterMeasure bad ≤ ((1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) := by
    rw [← one_div_two_pow_succ_add n]
    refine (Probability.PMF.toOuterMeasure_bind_le_add _ _
      {z_p | isNonresidueModPrime d.p z_p = false} bad
      ((1 / 2 ^ (n + 1) : ℝ≥0) : ℝ≥0∞) ?_).trans
      (add_le_add (toOuterMeasure_not_isNonresidueModPrime_le d.two_lt_p n) le_rfl)
    intro z_p _ hzp_good
    have hp_ok : isNonresidueModPrime d.p z_p = true :=
      Bool.eq_true_of_not_eq_false hzp_good
    refine (Probability.PMF.toOuterMeasure_bind_le_add _ _
      {z_q | isNonresidueModPrime d.q z_q = false} bad 0 ?_).trans ?_
    · intro z_q _ hzq_good
      have hq_ok : isNonresidueModPrime d.q z_q = true :=
        Bool.eq_true_of_not_eq_false hzq_good
      have hnot_bad :
          (textbookPublicKey d.p d.q z_p z_q, encPair encNat encNat (d.p, d.q)) ∉ bad := by
        intro hbad
        exact hbad ⟨KeyDesc.ofNonresidues d hp_ok hq_ok, rfl⟩
      rw [PMF.toOuterMeasure_pure_apply, ite_eq_right hnot_bad]
    · rw [add_zero]
      exact toOuterMeasure_not_isNonresidueModPrime_le d.two_lt_q n
  simp only [textbookKeyGen, ProbComp.eval_bind, ProbComp.eval_pure]
  rw [PMF.toOuterMeasure_bind_apply]
  calc
    ∑' d, ProbComp.eval (gen n) d * _
      ≤ ∑' d, ProbComp.eval (gen n) d * ((1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) :=
        tsum_le_tsum fun d => mul_le_mul_of_nonneg_left (hper d) zero_le
    _ = ((1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

private theorem closeTo_pure_of_bad_le {α β : Type} (μ : PMF α) (f : α → PMF β)
    (good : Set α) (b : β) {ε : ℝ≥0∞} (hbad : μ.toOuterMeasure goodᶜ ≤ ε)
    (hgood : ∀ a ∈ good, ∀ x ∈ (f a).support, x = b) :
    CloseTo (μ.bind f) (PMF.pure b) ε := by
  have hf_eq (a : α) (ha : a ∈ good) : f a = PMF.pure b := by
    ext x
    by_cases hxb : x = b
    · subst hxb
      rw [PMF.pure_apply, ite_eq_left rfl]
      have htot := (f a).tsum_coe
      rw [tsum_eq_single x] at htot
      · exact htot
      · intro y hy
        by_contra hne
        exact hy (hgood a ha y ((PMF.mem_support_iff _ _).mpr hne))
    · rw [PMF.pure_apply, ite_eq_right hxb, PMF.apply_eq_zero_iff]
      intro hmem
      exact hxb (hgood a ha x hmem)
  intro E
  rw [PMF.toOuterMeasure_bind_apply]
  calc
    ∑' a, μ a * (f a).toOuterMeasure E
      ≤ ∑' a, (good.indicator (fun a => μ a * (PMF.pure b).toOuterMeasure E) a +
          goodᶜ.indicator μ a) := by
        refine tsum_le_tsum fun a => ?_
        by_cases ha : a ∈ good
        · have hna : a ∉ goodᶜ := fun h => h ha
          simp only [Set.indicator_of_mem ha, Set.indicator_of_notMem hna, add_zero, hf_eq a ha,
            le_rfl]
        · have hca : a ∈ goodᶜ := ha
          simp only [Set.indicator_of_notMem ha, Set.indicator_of_mem hca, zero_add]
          exact mul_le_of_le_one_right zero_le (PMF.toOuterMeasure_le_one (f a) E)
    _ = ∑' a, good.indicator (fun a => μ a * (PMF.pure b).toOuterMeasure E) a +
        μ.toOuterMeasure goodᶜ := by
        rw [tsum_add, ← PMF.toOuterMeasure_apply]
    _ ≤ (PMF.pure b).toOuterMeasure E + ε := by
        refine add_le_add ?_ hbad
        calc
          ∑' a, good.indicator (fun a => μ a * (PMF.pure b).toOuterMeasure E) a
            ≤ ∑' a, μ a * (PMF.pure b).toOuterMeasure E :=
              tsum_le_tsum fun a => Set.indicator_le_self _ _ a
          _ = (PMF.pure b).toOuterMeasure E := by
              rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

private theorem closeTo_roundTrip_textbookKeyGen {Msg : Type}
    (encProg : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decFn : List Bool → List Bool → Msg)
    (gen : ℕ → ProbComp ModulusDesc) (n : ℕ) (msg : Msg)
    (hcorrect : ∀ (k : KeyDesc) {ct : List Bool},
      ct ∈ (ProbComp.eval (encProg n (encPair encNat encNat (k.modulus, k.z)) msg)).support →
      decFn (encPair encNat encNat (k.p, k.q)) ct = msg) :
    CloseTo
      (ProbComp.eval (do
        let keys ← textbookKeyGen gen n
        let ct ← encProg n keys.1 msg
        return decFn keys.2 ct))
      (PMF.pure msg) ((1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) := by
  let good : Set (List Bool × List Bool) :=
    {keys | ∃ k : KeyDesc,
      keys = (encPair encNat encNat (k.modulus, k.z), encPair encNat encNat (k.p, k.q))}
  rw [ProbComp.eval_bind]
  refine closeTo_pure_of_bad_le (ProbComp.eval (textbookKeyGen gen n))
    (fun keys => ProbComp.eval (do let ct ← encProg n keys.1 msg; return decFn keys.2 ct))
    good msg (toOuterMeasure_not_exists_keyDesc_textbookKeyGen_le gen n) ?_
  rintro keys ⟨k, hkeq⟩ out hout
  obtain ⟨hpk, hsk⟩ := Prod.ext_iff.mp hkeq
  rw [ProbComp.eval_bind, PMF.mem_support_bind_iff] at hout
  obtain ⟨ct, hct, hout_eq⟩ := hout
  rw [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hout_eq
  rw [hout_eq, hsk]
  rw [hpk] at hct
  exact hcorrect k hct

/-- Statistical round-trip decryption correctness for 1-bit Goldwasser–Micali under
`textbookKeyGen gen`: for every message bit `m`, generating keys and encrypting `m` decrypts to
`m` up to at most `1 / 2 ^ n` statistical distance (`CloseTo`). -/
theorem closeTo_decrypt_encrypt_textbookKeyGen (gen : ℕ → ProbComp ModulusDesc) (n : ℕ)
    (m : Bool) :
    CloseTo
      (ProbComp.eval (do
        let keys ← textbookKeyGen gen n
        let ct ← encrypt n keys.1 m
        return decrypt keys.2 ct))
      (PMF.pure m) ((1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) :=
  closeTo_roundTrip_textbookKeyGen encrypt decrypt gen n m fun k _ hct => k.decrypt_encrypt m hct

/-- Statistical round-trip decryption correctness for bitwise multi-bit Goldwasser–Micali under
`textbookKeyGen gen`: for every bit word `bits`, generating keys and encrypting `bits` with
`encryptWord` decrypts via `decryptWord` to `bits` up to at most `1 / 2 ^ n` statistical distance
(`CloseTo`). -/
theorem closeTo_decryptWord_encryptWord_textbookKeyGen (gen : ℕ → ProbComp ModulusDesc) (n : ℕ)
    (bits : List Bool) :
    CloseTo
      (ProbComp.eval (do
        let keys ← textbookKeyGen gen n
        let ct ← encryptWord n keys.1 bits
        return decryptWord keys.2 ct))
      (PMF.pure bits) ((1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) :=
  closeTo_roundTrip_textbookKeyGen encryptWord decryptWord gen n bits fun k _ hct =>
    Encryption.bitwiseDecrypt_bitwiseEncrypt (fun b _ h => k.decrypt_encrypt b h) bits hct

/-! ### Single-bit and multi-bit IND-CPA security from `QuadraticResiduosityHard` alone -/

/-- Quantitative single-bit IND-CPA step for `(textbookKeyGen gen, encrypt)` (after
[KatzLindell2020], Section 15.4.4, Theorem 15.29, locator not verified): when `gen n` draws
distinct odd primes of at least `n` bits, every adversary's IND-CPA advantage is at most twice
`qrDistinguisher adversary`'s QR advantage plus `12 / 2 ^ n` (`10 / 2 ^ n` from unit sampling and
`2 / 2 ^ n` from capped `QNR_N^{+1}` key generation). -/
theorem advantage_textbookGame_le_qr {gen : ℕ → ProbComp ModulusDesc} {n : ℕ}
    (hsize : ∀ d ∈ (ProbComp.eval (gen n)).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (adversary : Encryption.Adversary) :
    Encryption.advantage (Encryption.game (textbookKeyGen gen) encrypt adversary) n ≤
      2 * Game.advantage
        (qrRealGame (fun k => ProbComp.eval (gen k)) (qrDistinguisher adversary) n)
        (qrIdealGame (fun k => ProbComp.eval (gen k)) (qrDistinguisher adversary) n) +
      12 / 2 ^ n := by
  have hhop (bit : Bool) :
      Game.advantage
        (ProbComp.eval (Encryption.game (textbookKeyGen gen) encrypt adversary bit n))
        (Encryption.publicKeyGame (publicKeyLaw (fun k => ProbComp.eval (gen k)) n)
          encrypt adversary bit n) ≤
        1 / 2 ^ n := by
    rw [Encryption.eval_game_eq_publicKeyGame]
    exact Game.advantage_bind_le_of_closeTo (closeTo_textbookKeyGen_publicKeyLaw gen n) _
  have h4 := Game.advantage_four_hop_le (hhop false) (hhop true)
  exact (h4.trans (add_le_add (add_le_add le_rfl (advantage_publicKeyGame_le_qr hsize adversary))
    le_rfl)).trans_eq (by ring)

/-- Single-bit IND-CPA step for textbook Goldwasser–Micali encryption (`textbookKeyGen gen`,
`encrypt`) from `QuadraticResiduosityHard` alone (after [KatzLindell2020], Section 15.4.4,
Construction 15.28 and Theorem 15.29, locator not verified; pending primary-source verification for
registry enrollment). Let `gen` draw distinct odd `n`-bit primes (`ModulusDesc`, with no Blum
restriction). If quadratic residuosity is hard relative to `gen`, then `(textbookKeyGen gen,
encrypt)` satisfies `Encryption.INDCPA` against all uniform strict-PPT adversaries. Neither
indistinguishability of keys from an ideal law nor computability of `gen` is assumed. -/
theorem indcpa_textbookGoldwasserMicali {gen : ℕ → ProbComp ModulusDesc}
    (hsize : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (hQR : QuadraticResiduosityHard fun n => ProbComp.eval (gen n)) :
    Encryption.INDCPA (textbookKeyGen gen) encrypt := by
  intro adversary hA
  have hD := hQR (qrDistinguisher adversary) (isPPTOn_qrDistinguisher hA)
  refine negligible_of_le ((hD.add hD).add (negligible_const_div_two_pow 12)) fun n => ?_
  dsimp only [Pi.add_apply]; rw [← two_mul]
  exact advantage_textbookGame_le_qr (hsize n) adversary

/-- Encoded bit length of `textbookPublicKey p q z_p z_q` in terms of an upper bound `B` on
`p.size` and `q.size`, valid for all `z_p, z_q : ℕ` whenever `0 < p` and `0 < q`. -/
theorem length_textbookPublicKey_le {p q B : ℕ} (hp_pos : 0 < p) (hq_pos : 0 < q)
    (hp : p.size ≤ B) (hq : q.size ≤ B) (z_p z_q : ℕ) :
    (textbookPublicKey p q z_p z_q).length ≤ 6 * B + 1 := by
  have hmul : p * q < 2 ^ (2 * B) := by
    calc p * q < 2 ^ B * 2 ^ B := Nat.mul_lt_mul'' (Nat.size_le.mp hp) (Nat.size_le.mp hq)
      _ = 2 ^ (2 * B) := by rw [two_mul, pow_add]
  have hlt : crtCombineNat p q z_p z_q < p * q :=
    Nat.mod_lt _ (Nat.mul_pos hp_pos hq_pos)
  have hsizeN : (p * q).bits.length ≤ 2 * B :=
    Nat.size_eq_bits_len _ ▸ Nat.size_le.mpr hmul
  have hsizeZ : (crtCombineNat p q z_p z_q).bits.length ≤ 2 * B :=
    Nat.size_eq_bits_len _ ▸ Nat.size_le.mpr (lt_trans hlt hmul)
  simp only [textbookPublicKey, encPair_apply, List.length_append, length_frame, encNat_apply]
  omega

/-- Quantitative multi-bit IND-CPA step for `(textbookKeyGen gen, encryptWord)` on bounded-length
words (after [KatzLindell2020], Section 15.4.4, locator not verified): via lossy quadratic-residue
public keys, bitwise encryption of equal-length words of length at most `maxLen n` reduces to
`QuadraticResiduosityHard` with **factor-`2` loss** (independent of `maxLen n`) plus
`(10 * maxLen n + 2) / 2 ^ n`. -/
theorem advantage_textbookWordGame_le_qr (maxLen : ℕ → ℕ) {gen : ℕ → ProbComp ModulusDesc} {n : ℕ}
    (hsize : ∀ d ∈ (ProbComp.eval (gen n)).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (adversary : Encryption.WordAdversary) :
    Encryption.advantage
        (Encryption.gameOn (validBoundedWords maxLen) (textbookKeyGen gen) encryptWord adversary)
        n ≤
      2 * Game.advantage
        (qrRealGame (fun k => ProbComp.eval (gen k)) (qrWordDistinguisher maxLen adversary) n)
        (qrIdealGame (fun k => ProbComp.eval (gen k)) (qrWordDistinguisher maxLen adversary) n) +
      (10 * maxLen n + 2 : ℝ≥0) / 2 ^ n := by
  have hhop (bit : Bool) :
      Game.advantage
        (ProbComp.eval
          (Encryption.gameOn (validBoundedWords maxLen) (textbookKeyGen gen)
            encryptWord adversary bit n))
        (publicKeyWordGame maxLen (publicKeyLaw (fun k => ProbComp.eval (gen k)) n)
          adversary bit n) ≤
        1 / 2 ^ n := by
    rw [Encryption.eval_gameOn_eq_publicKeyGameOn]
    exact Game.advantage_bind_le_of_closeTo (closeTo_textbookKeyGen_publicKeyLaw gen n) _
  have h4 := Game.advantage_four_hop_le (hhop false) (hhop true)
  refine (h4.trans (add_le_add (add_le_add le_rfl
    (advantage_publicKeyWordGame_le_qr maxLen hsize adversary)) le_rfl)).trans_eq ?_
  ring

/-- Multi-bit IND-CPA step for textbook bitwise Goldwasser–Micali encryption (`textbookKeyGen gen`,
`encryptWord`) from `QuadraticResiduosityHard` alone (after [KatzLindell2020], Section 15.4.4,
Construction 15.28 and Theorem 15.29, locator not verified; pending primary-source verification for
registry enrollment). Let `gen` draw distinct odd primes (`ModulusDesc`, with no Blum restriction)
whose bit-lengths are at least `n` and at most `sizeBound n` for a polynomially bounded function
`sizeBound` (for example `fun n => n + c`, or the output cap of any uniform strict-PPT `gen`). If
quadratic residuosity is hard relative to `gen`, then `(textbookKeyGen gen, encryptWord)` satisfies
`Encryption.WordINDCPA` against all uniform strict-PPT word adversaries, with factor-`2` QR
reduction loss independent of message length (`advantage_textbookWordGame_le_qr`). -/
theorem wordINDCPA_textbookGoldwasserMicali {gen : ℕ → ProbComp ModulusDesc}
    {sizeBound : ℕ → ℕ} (hbound : PolynomiallyBounded sizeBound)
    (hsize : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (hupper : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support,
      d.p.size ≤ sizeBound n ∧ d.q.size ≤ sizeBound n)
    (hQR : QuadraticResiduosityHard fun n => ProbComp.eval (gen n)) :
    Encryption.WordINDCPA (textbookKeyGen gen) encryptWord := by
  intro adversary hadversary
  have hpkBound : PolynomiallyBounded (fun n => 6 * sizeBound n + 1) := by fun_prop
  obtain ⟨ck, dk, hpkPoly⟩ := polynomiallyBounded_iff_le.mp hpkBound
  obtain ⟨ca, da, hchooseLen⟩ := hadversary.choose.on.length_le
  let maxLen (n : ℕ) : ℕ := ca * (2 * n + 2 * (ck * (n + 1) ^ dk) + 4) ^ da
  have hmax : ComputableInPolyTime maxLen encUnary encUnary := by
    dsimp only [maxLen]; fun_prop
  have hmaxPoly : PolynomiallyBounded maxLen := hmax.polynomiallyBounded
  have hD := hQR (qrWordDistinguisher maxLen adversary)
    (isPPTOn_qrWordDistinguisher hmax hadversary)
  have htail :=
    ((negligible_const_div_two_pow 10).polynomiallyBounded_mul hmaxPoly).add
      (negligible_const_div_two_pow 2)
  have hbounded : Negligible (fun n => Encryption.advantage
      (Encryption.gameOn (validBoundedWords maxLen) (textbookKeyGen gen) encryptWord adversary)
      n) := by
    refine negligible_of_le ((hD.add hD).add htail) fun n => ?_
    dsimp only [Pi.add_apply]; rw [← two_mul]
    refine (advantage_textbookWordGame_le_qr maxLen (hsize n) adversary).trans (le_of_eq ?_)
    congr 1; push_cast; ring
  have heqGame (bit : Bool) (n : ℕ) :
      ProbComp.eval (Encryption.gameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
        (textbookKeyGen gen) encryptWord adversary bit n) =
      ProbComp.eval (Encryption.gameOn (validBoundedWords maxLen)
        (textbookKeyGen gen) encryptWord adversary bit n) := by
    simp only [Encryption.gameOn, pmf_norm, apply_ite ProbComp.eval]
    refine Probability.PMF.bind_congr_on_support _ _ _ fun keys hkeys =>
      Probability.PMF.bind_congr_on_support _ _ _ fun choice hchoice => ?_
    have hpkLen : keys.1.length ≤ 6 * sizeBound n + 1 := by
      obtain ⟨d, hd, z_p, z_q, rfl⟩ := exists_of_mem_support_textbookKeyGen hkeys
      exact length_textbookPublicKey_le d.prime_p.pos d.prime_q.pos
        (hupper n d hd).1 (hupper n d hd).2 z_p z_q
    have hmsgLen : (ChoiceOut.msg₀ choice).length ≤ maxLen n := by
      have hout := hchooseLen (n, keys.1) choice hchoice
      have hk : keys.1.length ≤ ck * (n + 1) ^ dk := hpkLen.trans (hpkPoly n)
      have hin : (encPair encUnary encBits (n, keys.1)).length + 1 ≤
          2 * n + 2 * (ck * (n + 1) ^ dk) + 4 := by
        enc_len
      have hm₀ : (ChoiceOut.msg₀ choice).length ≤ (encChoiceOut encBits choice).length := by
        dsimp only [ChoiceOut.msg₀, ChoiceOut.msgs]; enc_len
      exact hm₀.trans (hout.trans (Nat.mul_le_mul_left ca (Nat.pow_le_pow_left hin da)))
    simp only [validBoundedWords, decide_eq_true hmsgLen, Bool.and_true]
  refine hbounded.congr fun n => ?_
  dsimp only [Encryption.advantage]
  rw [heqGame false n, heqGame true n]

end Cslib.Crypto.GoldwasserMicali
