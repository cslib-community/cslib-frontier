/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Crypto.Computational.ElGamal.KDF
import CslibFrontier.Crypto.Computational.ElGamal.KeyDerivation
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Negligible.InversePolynomial
import Mathlib.NumberTheory.Bertrand

set_option linter.privateModule false

/-!
# Checked non-vacuity witnesses for `PrimeOrderGroupFamily.LinearHashKDFConditions`

Ordinary `module` client (no `import all`) supplying positive and negative non-vacuity checks for
`PrimeOrderGroupFamily.LinearHashKDFConditions` (`ElGamal/KDF.lean`):

1. **Concrete group family (`additivePrimeGroups`):** additive cyclic groups `(ZMod q, +)` of
   prime order `q`, with little-endian residue encoding and binary-arithmetic `ComputableInPolyTime`
   certificates.
2. **Satisfying instance (`linearHashKDFConditions_bertrand`):** picks a prime order
   `q ∈ (2^(2n + 1), 2^(2n + 2))` via Bertrand's postulate (`bertrandPrimeDesc`, `bertrandSetup`)
   and discharges all five fields of `LinearHashKDFConditions` unconditionally for growing key
   length `msgLen n = n + 1`, yielding unconditional `SecureKDF`
   (`secureKDF_additivePrimeGroups_bertrand`) and `KeyDerivation.Secure`
   (`keyDerivation_secure_additivePrimeGroups`) instantiations.
3. **Refuting instance (`not_linearHashKDFConditions_fixedTwo`):** proves
   `LinearHashKDFConditions` fails when the group order stays fixed at `2` with constant `1`-bit
   output length, regardless of `keyLen`, `bound`, and `qMin`.
-/

namespace CslibFrontierTests.Crypto.LinearHashKDFNonvacuity

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.PrimeOrderGroupFamily Turing.MultiTapeTM
open scoped NNReal

/-- Description of an additive cyclic prime-order group: a prime natural number `q`. -/
private abbrev PrimeDesc : Type := { q : ℕ // q.Prime }

private def encPrimeDesc : PrimeDesc ↪ List Bool :=
  (Function.Embedding.subtype _).trans encNat

private theorem computableInPolyTime_primeDesc_val :
    ComputableInPolyTime (Subtype.val : PrimeDesc → ℕ) encPrimeDesc encNat :=
  ComputableInPolyTime.of_eq fun _ => rfl

/-- Additive prime-order cyclic groups `(ZMod q, +)` with generator `1` and little-endian binary
residue encoding `x.val.bits`. -/
def additivePrimeGroups : PrimeOrderGroupFamily where
  Desc := PrimeDesc
  encDesc := encPrimeDesc
  order d := d.val
  prime_order d := d.2
  Carrier d := ZMod d.val
  generator _ := 1
  card_carrier d := Nat.card_zmod d.val
  generator_ne_zero d := fun h => by
    have hval := congrArg ZMod.val h
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt d.2.one_lt, ZMod.val_zero] at hval
    exact one_ne_zero hval
  encode _ x := x.val.bits
  encode_injective d _ _ h := @ZMod.val_injective d.val ⟨d.2.ne_zero⟩ _ _ (encNat.injective h)
  add | (d, x, y) => ((ofBits x + ofBits y) % d.val).bits
  add_encode d x y := by
    simp only [ofBits_bits]
    exact (congrArg Nat.bits (@ZMod.val_add d.val ⟨d.2.ne_zero⟩ x y)).symm
  smul | (d, a, x) => ((a * ofBits x) % d.val).bits
  smul_encode d a x := by
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
    simp only [ofBits_bits]
    rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
  computableInPolyTime_order := computableInPolyTime_primeDesc_val
  computableInPolyTime_generator := by
    have hconst : ComputableInPolyTime (fun _ : PrimeDesc => ([true] : List Bool))
        encPrimeDesc encBits :=
      ComputableInPolyTime.const [true]
    exact hconst.of_enc_eq fun d => by
      have : Fact (1 < d.val) := ⟨d.2.one_lt⟩
      rw [ZMod.val_one]
      rfl
  computableInPolyTime_add := by
    have hp := ComputableInPolyTime.id'
      (encIn := encDescBitsPair encPrimeDesc)
    have hd := computableInPolyTime_primeDesc_val.comp hp.fst'
    have hx := ComputableInPolyTime.bitsToNat.comp hp.snd'.fst'
    have hy := ComputableInPolyTime.bitsToNat.comp hp.snd'.snd'
    simpa only [encNat_apply, Function.comp_def] using
      (ComputableInPolyTime.binary_mod' (ComputableInPolyTime.binary_add' hx hy) hd).encoding_comp
  computableInPolyTime_smul := by
    have hp := ComputableInPolyTime.id'
      (encIn := encPair encPrimeDesc (encPair encNat encBits))
    have hd := computableInPolyTime_primeDesc_val.comp hp.fst'
    have ha := hp.snd'.fst'
    have hx := ComputableInPolyTime.bitsToNat.comp hp.snd'.snd'
    simpa only [encNat_apply, Function.comp_def] using
      (ComputableInPolyTime.binary_mod' (ComputableInPolyTime.binary_mul' ha hx) hd).encoding_comp

private theorem exists_prime_between_two_pow (n : ℕ) :
    ∃ q : ℕ, q.Prime ∧ 2 ^ (2 * n + 1) < q ∧ q ≤ 2 ^ (2 * n + 2) := by
  obtain ⟨q, hqp, hlt, hle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (2 ^ (2 * n + 1)) (Nat.ne_of_gt (Nat.two_pow_pos _))
  refine ⟨q, hqp, hlt, ?_⟩
  simpa only [Nat.pow_succ, mul_comm] using hle

/-- Prime description chosen in `(2 ^ (2 * n + 1), 2 ^ (2 * n + 2)]` via Bertrand's postulate. -/
noncomputable def bertrandPrimeDesc (n : ℕ) : additivePrimeGroups.Desc :=
  ⟨Classical.choose (exists_prime_between_two_pow n),
    (Classical.choose_spec (exists_prime_between_two_pow n)).1⟩

private theorem two_pow_lt_bertrandPrimeDesc (n : ℕ) :
    2 ^ (2 * n + 1) < (bertrandPrimeDesc n).val :=
  (Classical.choose_spec (exists_prime_between_two_pow n)).2.1

private theorem bertrandPrimeDesc_lt_two_pow (n : ℕ) :
    (bertrandPrimeDesc n).val < 2 ^ (2 * n + 2) := by
  have hspec := Classical.choose_spec (exists_prime_between_two_pow n)
  have hle : (bertrandPrimeDesc n).val ≤ 2 ^ (2 * n + 2) := hspec.2.2
  refine lt_of_le_of_ne hle fun heq => ?_
  have hp : (2 ^ (2 * n + 2)).Prime := heq ▸ hspec.1
  have hgt : 2 < 2 ^ (2 * n + 2) := by
    have : 2 ^ 1 < 2 ^ (2 * n + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    simpa only [pow_one] using this
  have hdvd : 2 ∣ 2 ^ (2 * n + 2) := dvd_pow_self 2 (by omega)
  exact absurd (hp.eq_one_or_self_of_dvd 2 hdvd) (by omega)

private theorem bits_length_bertrandPrimeDesc (n : ℕ) :
    (bertrandPrimeDesc n).val.bits.length = 2 * n + 2 := by
  have hle : (bertrandPrimeDesc n).val.size ≤ 2 * n + 2 :=
    Nat.size_le.mpr (bertrandPrimeDesc_lt_two_pow n)
  have hlt : 2 * n + 1 < (bertrandPrimeDesc n).val.size :=
    Nat.lt_size.mpr (Nat.le_of_lt (two_pow_lt_bertrandPrimeDesc n))
  rw [← encNat_apply, length_encNat_eq_size]
  omega

/-- Deterministic growing-prime setup law using `bertrandPrimeDesc`. -/
noncomputable def bertrandSetup (n : ℕ) : PMF additivePrimeGroups.Desc :=
  PMF.pure (bertrandPrimeDesc n)

/-- Output key length computed from a group description: half the binary length of its order. -/
def halfOrderBitsLen (d : additivePrimeGroups.Desc) : ℕ :=
  (additivePrimeGroups.encDesc d).length / 2

/-- Encoding length bound computed from a group description: the binary length of its order. -/
def orderBitsBound (d : additivePrimeGroups.Desc) : ℕ :=
  (additivePrimeGroups.encDesc d).length

private theorem computableInPolyTime_halfOrderBitsLen :
    ComputableInPolyTime halfOrderBitsLen additivePrimeGroups.encDesc encUnary := by
  unfold halfOrderBitsLen
  exact (ComputableInPolyTime.unary_div_const 2).comp
    (ComputableInPolyTime.encoding_length additivePrimeGroups.encDesc)

private theorem computableInPolyTime_orderBitsBound :
    ComputableInPolyTime orderBitsBound additivePrimeGroups.encDesc encUnary := by
  unfold orderBitsBound
  exact ComputableInPolyTime.encoding_length additivePrimeGroups.encDesc

/-- Concrete satisfying instance of `PrimeOrderGroupFamily.LinearHashKDFConditions` with
growing output length `msgLen n = n + 1` and group order exceeding `2 ^ (2 * n + 1)`. -/
theorem linearHashKDFConditions_bertrand :
    additivePrimeGroups.LinearHashKDFConditions bertrandSetup halfOrderBitsLen orderBitsBound
      (fun n => n + 1) (fun n => 2 ^ (2 * n + 1)) where
  qMin_pos _ := Nat.two_pow_pos _
  keyLen_eq n d hd := by
    simp only [bertrandSetup, PMF.support_pure, Set.mem_singleton_iff] at hd
    subst hd
    change (encNat (bertrandPrimeDesc n).val).length / 2 = n + 1
    rw [encNat_apply, bits_length_bertrandPrimeDesc]
    omega
  length_encode_le _ d _ x := by
    have : NeZero d.val := ⟨d.2.ne_zero⟩
    change (encNat x.val).length ≤ (encNat d.val).length
    exact length_encNat_mono (Nat.le_of_lt x.val_lt)
  qMin_le_order n d hd := by
    simp only [bertrandSetup, PMF.support_pure, Set.mem_singleton_iff] at hd
    subst hd
    exact Nat.le_of_lt (two_pow_lt_bertrandPrimeDesc n)
  negligible := by
    have hfun : (fun n => (2 : ℝ≥0) ^ (n + 1) / ((2 ^ (2 * n + 1) : ℕ) : ℝ≥0)) =
        fun n => (2 ^ n : ℝ≥0)⁻¹ := by
      funext n
      push_cast
      have hpow : (2 : ℝ≥0) ^ (2 * n + 1) = 2 ^ (n + 1) * 2 ^ n := by
        rw [← pow_add]; congr 1; omega
      rw [hpow, div_mul_eq_div_div, div_self (pow_ne_zero _ two_ne_zero), one_div]
    rw [hfun]
    exact negligible_inv_two_pow

/-- Unconditional `SecureKDF` instantiation for positive growing output length `n + 1`, with all
hypotheses of `LinearHashKDFConditions` discharged. -/
theorem secureKDF_additivePrimeGroups_bertrand :
    additivePrimeGroups.withSeed.SecureKDF
      (additivePrimeGroups.seededSetup bertrandSetup
        (additivePrimeGroups.linearHashSeedLen (fun n => n + 1) orderBitsBound))
      (additivePrimeGroups.linearHashKDF halfOrderBitsLen orderBitsBound)
      (fun n => n + 1) :=
  additivePrimeGroups.secureKDF_linearHashKDF linearHashKDFConditions_bertrand

/-- The linear-hash KDF over `additivePrimeGroups` is executable in polynomial time and is an
unconditional `KeyDerivation.Secure` instance via `secureKDF_iff_keyDerivation`. -/
theorem keyDerivation_secure_additivePrimeGroups :
    ComputableInPolyTime
        (additivePrimeGroups.linearHashKDF halfOrderBitsLen orderBitsBound)
        (encPair additivePrimeGroups.withSeed.encDesc encBits) encBits ∧
      KeyDerivation.Secure additivePrimeGroups.withSeed.encCDHInput encBits
        (additivePrimeGroups.withSeed.kdfSecret
          (additivePrimeGroups.seededSetup bertrandSetup
            (additivePrimeGroups.linearHashSeedLen (fun n => n + 1) orderBitsBound)))
        PrimeOrderGroupFamily.DDHInput.toCDHInput
        (fun x => additivePrimeGroups.linearHashKDF halfOrderBitsLen orderBitsBound
          (x.groupParameters,
            additivePrimeGroups.withSeed.encode x.groupParameters x.candidateShared))
        (fun n => BitString.uniformList (n + 1)) :=
  ⟨additivePrimeGroups.computableInPolyTime_linearHashKDF
      computableInPolyTime_halfOrderBitsLen computableInPolyTime_orderBitsBound,
    (additivePrimeGroups.withSeed.secureKDF_iff_keyDerivation _ _ _).mp
      secureKDF_additivePrimeGroups_bertrand⟩

/-- Fixed group of order `2` in `additivePrimeGroups`. -/
private def fixedTwoDesc : additivePrimeGroups.Desc :=
  ⟨2, Nat.prime_two⟩

private theorem order_fixedTwoDesc : additivePrimeGroups.order fixedTwoDesc = 2 := rfl

/-- Negative witness: `LinearHashKDFConditions` fails when the group order remains fixed at `2`
with constant 1-bit output length, regardless of `keyLen`, `bound`, and `qMin`. -/
theorem not_linearHashKDFConditions_fixedTwo (keyLen _bound : additivePrimeGroups.Desc → ℕ)
    (qMin : ℕ → ℕ) :
    ¬ additivePrimeGroups.LinearHashKDFConditions
        (fun _ => PMF.pure fixedTwoDesc) keyLen _bound (fun _ => 1) qMin := by
  intro h
  have hle : ∀ n, (1 : ℝ≥0) ≤ (2 : ℝ≥0) ^ 1 / (qMin n : ℝ≥0) := fun n => by
    have hq_pos : (0 : ℝ≥0) < qMin n := Nat.cast_pos.mpr (h.qMin_pos n)
    have hq_le : qMin n ≤ 2 := by
      simpa only [order_fixedTwoDesc] using
        h.qMin_le_order n fixedTwoDesc (by simp only [PMF.support_pure, Set.mem_singleton_iff])
    rw [pow_one, one_le_div₀ hq_pos]
    exact_mod_cast hq_le
  exact not_negligible_const one_ne_zero (negligible_of_le h.negligible hle)

end CslibFrontierTests.Crypto.LinearHashKDFNonvacuity
