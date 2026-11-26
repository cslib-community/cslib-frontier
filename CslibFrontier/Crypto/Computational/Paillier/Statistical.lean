/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Paillier
public import CslibFrontier.Crypto.Computational.Paillier.Finite
public import CslibFrontier.Probability.StatisticalDistance.CloseTo
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Foundations.Data.ZMod.Basic

/-!
# Statistical homomorphism of word-encoded Paillier encryption

The word algorithm `Paillier.encrypt` samples a residue using fair coins and replaces nonunits
by `1`. Its randomness is close to uniform on the units, but is not exactly uniform. This module
compares that implemented ciphertext distribution with `paillierEncrypt`, which samples a
uniform unit, and transfers the latter's exact additive homomorphism to statistical closeness.

For a balanced modulus `N = p * q` with both factors having at least `n` bits, word encryption
is within `5 / 2 ^ n` of encoded uniform-unit encryption. Multiplying a supported ciphertext of
`m₁` by a fresh word encryption of `m₂` is within `10 / 2 ^ n` of fresh word encryption of
`m₁ + m₂`. The same bound holds for two independently sampled ciphertexts: the first ciphertext
can be fixed throughout the comparison, so it incurs no additional sampling error.

These original approximation bounds are unconditional results for the existing word algorithms.
They do not assert the exact distributional condition of [KatzLindell2020], Definition 15.14,
which fails for this sampler, or introduce a new security assumption. `CloseTo` quantifies over
every event on the full ciphertext words and is preserved by any deterministic or randomized
continuation.

## Main results

* `Cslib.Crypto.Paillier.closeTo_encrypt_paillierEncrypt`: the word encryption law is close to the
  encoded uniform-unit encryption law.
* `Cslib.Crypto.Paillier.closeTo_addCiphertexts_encrypt`: multiplying a supported ciphertext by
  fresh encryption is close to fresh encryption of the sum.
* `Cslib.Crypto.Paillier.closeTo_addCiphertexts`: the product of two independent encryptions is
  close to fresh encryption of the sum.
-/

public section

namespace Cslib.Crypto.Paillier

open Probability Turing.MultiTapeTM BalancedModulus
open scoped ENNReal NNReal

private theorem ciphertext_eq_val (N : ℕ) [NeZero N] (m r : ℕ) (hr : r.Coprime N) :
    ciphertext N m r =
      ((oneAddPowHom N (.ofAdd (m : ZMod N)) *
        powSelfHom N (ZMod.unitOfCoprime r hr) : (ZMod (N ^ 2))ˣ) : ZMod (N ^ 2)).val := by
  have h : (ciphertext N m r : ZMod (N ^ 2)) =
      (oneAddPowHom N (.ofAdd (m : ZMod N)) *
        powSelfHom N (ZMod.unitOfCoprime r hr) : (ZMod (N ^ 2))ˣ) := by
    rw [natCast_ciphertext (NeZero.ne N)]
    simp only [oneAddPowHom_apply, toAdd_ofAdd, ZMod.val_natCast, ← oneAddUnit_pow_mod,
      powSelfHom_apply, Units.val_mul, Units.val_pow_eq_pow_val, coe_oneAddUnit, coe_liftUnit,
      ZMod.coe_unitOfCoprime, ← ZMod.natCast_pow_self_mod]
  rw [← h, ZMod.val_natCast]
  simp only [ciphertext, Nat.mod_mod]

/-- Word encryption with the actual dyadic sampler is within `5 / 2 ^ n` of encryption with
uniform unit randomness, with both laws represented by the same ciphertext words. -/
theorem closeTo_encrypt_paillierEncrypt (d : Desc) (n m : ℕ)
    (hsize : n ≤ d.p.size ∧ n ≤ d.q.size) :
    CloseTo (ProbComp.eval (encrypt n (encNat d.modulus) m))
      ((ProbComp.eval (paillierEncrypt d.modulus (m : ZMod d.modulus))).map
        (fun c : (ZMod (d.modulus ^ 2))ˣ => encNat (c : ZMod (d.modulus ^ 2)).val))
      (5 / 2 ^ n) := by
  suffices h : CloseTo (ProbComp.eval (encrypt n (encNat d.modulus) m))
      ((ProbComp.eval (paillierEncrypt d.modulus (m : ZMod d.modulus))).map
        (fun c : (ZMod (d.modulus ^ 2))ˣ => encNat (c : ZMod (d.modulus ^ 2)).val))
      (↑((5 : ℝ≥0) / 2 ^ n)) by
    simpa only [ENNReal.coe_div (pow_ne_zero _ two_ne_zero), ENNReal.coe_pow,
      ENNReal.coe_ofNat] using h
  refine Game.closeTo_iff_forall_advantage_bind_le.2 fun test => ?_
  have h := Game.advantage_sampleModNat_units_le d.property.prime_fst d.property.prime_snd
    d.property.fst_ne_snd hsize.1 hsize.2
    (fun r => test (encNat (ciphertext d.modulus m (unitOrOne d.modulus r))))
  simp only [encrypt, ofBits_encNat, paillierEncrypt, ProbComp.eval_bind,
    ProbComp.eval_uniform, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, PMF.bind_map,
    Function.comp_apply]
  convert h using 1
  congr 2
  funext u
  rw [unitOrOne_val_coe_unit, ciphertext_eq_val d.modulus m _ (ZMod.val_coe_unit_coprime u),
    ZMod.unitOfCoprime_val]

/-- Multiplying any supported word ciphertext of `m₁` by a fresh word encryption of `m₂` is
within `10 / 2 ^ n` of fresh word encryption of `m₁ + m₂`. Only the fresh randomness is replaced
by uniform unit randomness in the comparison. -/
theorem closeTo_addCiphertexts_encrypt (d : Desc) (n m₁ m₂ : ℕ)
    (hsize : n ≤ d.p.size ∧ n ≤ d.q.size) {ct₁ : List Bool}
    (hct₁ : ct₁ ∈ (ProbComp.eval (encrypt n (encNat d.modulus) m₁)).support) :
    CloseTo
      ((ProbComp.eval (encrypt n (encNat d.modulus) m₂)).map
        (addCiphertexts (encNat d.modulus) ct₁))
      (ProbComp.eval (encrypt n (encNat d.modulus) (m₁ + m₂))) (10 / 2 ^ n) := by
  obtain ⟨r₁, hr₁, rfl⟩ := exists_of_mem_support_encrypt hct₁
  let c₁ : (ZMod (d.modulus ^ 2))ˣ :=
    oneAddPowHom d.modulus (.ofAdd (m₁ : ZMod d.modulus)) *
      powSelfHom d.modulus (ZMod.unitOfCoprime r₁ hr₁)
  have hc₁ : c₁ ∈ (ProbComp.eval
      (paillierEncrypt d.modulus (m₁ : ZMod d.modulus))).support :=
    mem_support_paillierEncrypt.2 ⟨ZMod.unitOfCoprime r₁ hr₁, rfl⟩
  have hideal :
      (((ProbComp.eval (paillierEncrypt d.modulus (m₂ : ZMod d.modulus))).map
        (fun c : (ZMod (d.modulus ^ 2))ˣ => encNat (c : ZMod (d.modulus ^ 2)).val)).map
        (addCiphertexts (encNat d.modulus) (encNat (ciphertext d.modulus m₁ r₁)))) =
      (ProbComp.eval (paillierEncrypt d.modulus ((m₁ + m₂ : ℕ) : ZMod d.modulus))).map
        (fun c : (ZMod (d.modulus ^ 2))ˣ => encNat (c : ZMod (d.modulus ^ 2)).val) := by
    calc
      _ = ((ProbComp.eval (paillierEncrypt d.modulus (m₂ : ZMod d.modulus))).map
          (c₁ * ·)).map
          (fun c : (ZMod (d.modulus ^ 2))ˣ => encNat (c : ZMod (d.modulus ^ 2)).val) := by
        simp only [PMF.map_comp]
        congr 1
        funext c₂
        simp only [Function.comp_apply, addCiphertexts, ofBits_encNat,
          ciphertext_eq_val d.modulus m₁ r₁ hr₁, c₁, Units.val_mul, ZMod.val_mul]
      _ = _ := by simp only [eval_mul_paillierEncrypt hc₁, Nat.cast_add]
  have h := (closeTo_encrypt_paillierEncrypt d n m₂ hsize).map
    (addCiphertexts (encNat d.modulus) (encNat (ciphertext d.modulus m₁ r₁)))
  rw [hideal] at h
  simpa only [← ENNReal.add_div, show (5 : ℝ≥0∞) + 5 = 10 by norm_num] using
    h.trans (closeTo_encrypt_paillierEncrypt d n (m₁ + m₂) hsize).symm

/-- Multiplying two independent word encryptions is within `10 / 2 ^ n` of fresh word
encryption of the sum. The bound is uniform in the first ciphertext, so averaging over it adds
no error. -/
theorem closeTo_addCiphertexts (d : Desc) (n m₁ m₂ : ℕ)
    (hsize : n ≤ d.p.size ∧ n ≤ d.q.size) :
    CloseTo (ProbComp.eval (do
        let ct₁ ← encrypt n (encNat d.modulus) m₁
        let ct₂ ← encrypt n (encNat d.modulus) m₂
        return addCiphertexts (encNat d.modulus) ct₁ ct₂))
      (ProbComp.eval (encrypt n (encNat d.modulus) (m₁ + m₂))) (10 / 2 ^ n) := by
  simpa only [ProbComp.eval_bind, ProbComp.eval_pure, ← PMF.bind_pure_comp, Function.comp_def,
    PMF.bind_const] using CloseTo.bind_right (ProbComp.eval (encrypt n (encNat d.modulus) m₁))
      fun _ => closeTo_addCiphertexts_encrypt d n m₁ m₂ hsize

end Cslib.Crypto.Paillier
