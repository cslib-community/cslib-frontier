/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.Encryption.Bitwise
import CslibFrontier.Crypto.Computational.Encryption.PublicKeyCPA
import CslibFrontier.Crypto.Computational.GoldwasserMicali.TextbookKeyGen
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Tactic.PolyTime
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.NormNum.Prime

/-!
# Module Client Tests for Textbook Goldwasser–Micali `QNR_N^{+1}` Key Generation

Ordinary-import `module` client tests for
`CslibFrontier.Crypto.Computational.GoldwasserMicali.TextbookKeyGen`:

* **Non-Blum model-boundary witness `(p, q) = (5, 13)` (`N = 65`)**: both primes satisfy
  `p ≡ q ≡ 1 (mod 4)` (`¬ IsBlumModulus 5 13`), so `-1 = 64 = 8 ^ 2 (mod 65)` is a quadratic
  residue and `blumKeyGen` fails decryption with probability `1` on `m = true` (every supported
  ciphertext of `encrypt n (blumPublicKey 65) true` decrypts under `sk = ⟨5, 13⟩` to `false`),
  whereas `textbookKeyGen` produces `z ∈ QNR_65^{+1}`
  (`crtCombine 5 13 (3 % 5) 2 (BinaryGcd.modInv 5 13) = 28`), decrypts
  both single bits and arbitrary bit words deterministically on accepted trials, and achieves
  `≤ 1 / 2 ^ n` statistical distance from `publicKeyLaw` and `≤ 1 / 2 ^ n` round-trip decryption
  failure at every `n : ℕ`;
* **Range and Euler-criterion boundary checks** for `isNonresidueModPrime`: `0`, `1`, `p - 1` (for
  `p = 5` where `-1` is a square), `p`, and out-of-range `p + 2 = 7` (even though `7 ≡ 2 (mod 5)`
  is a nonresidue, verifying the `a < p` guard that prevents modular wrap-around bias);
* **Security client instantiations**: `indcpa_textbookGoldwasserMicali`,
  `wordINDCPA_textbookGoldwasserMicali` (and its lift to `WordINDCPAOracle`), quantitative bounds
  `advantage_textbookGame_le_qr` and `advantage_textbookWordGame_le_qr` (factor-`2` QR loss
  independent of message length), and `INDCPA.wordINDCPA_bitwiseEncrypt` via
  `isPPTOn_textbookKeyGen` when `gen` is uniform strict PPT (eliminating `sizeBound` / `hupper`);
* **Unconditional joint satisfiability** of all modulus premises (`hbound`, `hsize`, `hupper` with
  `sizeBound n = n + 4`) at every `n : ℕ` via Bertrand's postulate
  (`Nat.exists_prime_lt_and_le_two_mul`), leaving `QuadraticResiduosityHard` as the sole hypothesis
  of `indcpa_textbookGoldwasserMicali` and `wordINDCPA_textbookGoldwasserMicali`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.GoldwasserMicaliTextbook

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Encryption Cslib.Crypto.GoldwasserMicali
open Turing.MultiTapeTM
open scoped NNReal ENNReal

/-! ### Non-Blum boundary witness `(p, q) = (5, 13)` (`N = 65`, `5 ≡ 13 ≡ 1 (mod 4)`) -/

private def d65 : ModulusDesc := ⟨5, 13, by norm_num, by norm_num, by decide, by decide, by decide⟩

private noncomputable def constNonBlumGen : ℕ → ProbComp ModulusDesc := fun _ => pure d65

private theorem crtCombine_5_13_eq_28 :
    crtCombine 5 13 (3 % 5) 2 (BinaryGcd.modInv 5 13) = 28 :=
  crtCombine_eq (by decide) (by decide) (by decide) _ <| by
    have h := BinaryGcd.mul_modInv_modEq_one (m := 13) (a := 5) (by decide) (by decide)
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, Nat.cast_one, mul_comm] at h
    exact h

/-- `(5, 13)` is a valid `ModulusDesc` that is **not** a Blum modulus (`5 % 4 = 1`, `13 % 4 = 1`),
and `isNonresidueModPrime` enforces `0 < a < p` and Euler's criterion (rejecting `0`, `1`, the
square `-1 ≡ 4 (mod 5)`, `p = 5`, and out-of-range `7 ≡ 2 (mod 5)` while accepting `2` and `3`). -/
theorem nonBlum_boundary_checks_65 :
    ¬ IsBlumModulus d65.p d65.q ∧
    isNonresidueModPrime 5 0 = false ∧
    isNonresidueModPrime 5 1 = false ∧
    isNonresidueModPrime 5 2 = true ∧
    isNonresidueModPrime 5 3 = true ∧
    isNonresidueModPrime 5 4 = false ∧
    isNonresidueModPrime 5 5 = false ∧
    isNonresidueModPrime 5 7 = false ∧
    isNonresidueModPrime 13 2 = true ∧
    isNonresidueModPrime 13 12 = false ∧
    crtCombine 5 13 (3 % 5) 2 (BinaryGcd.modInv 5 13) = 28 ∧
    28 % 5 = 3 ∧
    28 % 13 = 2 := by
  refine ⟨?_, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, crtCombine_5_13_eq_28, by decide, by decide⟩
  change ¬ IsBlumModulus 5 13
  rintro ⟨⟨_, h5⟩, _⟩
  omega

/-- Separation against `blumKeyGen` at `N = 65 = 5 * 13`: because `64 = 8 ^ 2` is a quadratic
residue modulo `65`, **every** ciphertext produced by `encrypt n (blumPublicKey 65) true` decrypts
under `sk = ⟨5, 13⟩` to `false` (`blumKeyGen` fails decryption with probability `1` on `true`). -/
theorem blumKeyGen_fails_decrypt_65 (n : ℕ) {ct : List Bool}
    (hct : ct ∈ (ProbComp.eval (encrypt n (blumPublicKey (d65.p * d65.q)) true)).support) :
    decrypt (encPair encNat encNat (d65.p, d65.q)) ct = false := by
  have hpk : blumPublicKey (d65.p * d65.q) = encPair encNat encNat (65, 64) := rfl
  rw [hpk] at hct
  obtain ⟨r, hr, rfl⟩ := exists_of_mem_support_encrypt rfl hct
  change decrypt (encPair encNat encNat (5, 13)) (encNat (ciphertext 65 64 true r)) = false
  rw [decrypt_encPair]
  have h64 : ((64 : ℕ) : ZMod 65) = (8 : ZMod 65) ^ 2 := by decide
  have h8_cop : Nat.Coprime 8 65 := by decide
  let u : (ZMod 65)ˣ := ZMod.unitOfCoprime (8 * r) (h8_cop.mul_left hr)
  have hct_eq : ciphertext 65 64 true r = (u ^ 2).val.val := by
    have hcast : ((ciphertext 65 64 true r : ℕ) : ZMod 65) = ((u ^ 2 : (ZMod 65)ˣ) : ZMod 65) := by
      rw [natCast_ciphertext (by decide : 65 ≠ 0), ite_eq_left rfl, h64, Units.val_pow_eq_pow_val,
        ZMod.coe_unitOfCoprime, Nat.cast_mul]
      ring
    rw [← ZMod.val_natCast_of_lt (a := ciphertext 65 64 true r) (Nat.mod_lt _ (by decide))]
    exact congrArg ZMod.val hcast
  rw [hct_eq]
  exact (decryptNat_unit_eq d65 (u ^ 2)).trans (decide_eq_false (not_not.mpr (IsSquare.sq u)))

/-- On the same non-Blum modulus `N = 65 = 5 * 13`, `textbookPublicKey 5 13 3 2` (`z = 28 ∈
QNR_65^{+1}`) achieves exact deterministic round-trip decryption on all single bits and bit words,
and `textbookKeyGen constNonBlumGen` achieves `1 / 2 ^ n` statistical closeness to `publicKeyLaw`
and `1 / 2 ^ n` statistical round-trip correctness at every `n : ℕ`. -/
theorem textbookKeyGen_succeeds_65 (n : ℕ) (m : Bool) (bits : List Bool) :
    (∀ ct ∈ (ProbComp.eval (encrypt n (textbookPublicKey 5 13 3 2) m)).support,
      decrypt (encPair encNat encNat (5, 13)) ct = m) ∧
    (∀ ct ∈ (ProbComp.eval (encryptWord n (textbookPublicKey 5 13 3 2) bits)).support,
      decryptWord (encPair encNat encNat (5, 13)) ct = bits) ∧
    CloseTo ((ProbComp.eval (textbookKeyGen constNonBlumGen n)).map Prod.fst)
      (publicKeyLaw (fun k => ProbComp.eval (constNonBlumGen k)) n)
      ((1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) ∧
    CloseTo
      (ProbComp.eval (do
        let keys ← textbookKeyGen constNonBlumGen n
        let ct ← encryptWord n keys.1 bits
        return decryptWord keys.2 ct))
      (PMF.pure bits) ((1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) :=
  ⟨fun _ hct => decrypt_encrypt_of_isNonresidueModPrime d65 (by decide) (by decide) m hct,
   fun _ hct => decryptWord_encryptWord_of_isNonresidueModPrime d65 (by decide) (by decide) bits
     hct,
   closeTo_textbookKeyGen_publicKeyLaw constNonBlumGen n,
   closeTo_decryptWord_encryptWord_textbookKeyGen constNonBlumGen n bits⟩

/-- Concrete check of `length_textbookPublicKey_le`, `KeyDesc.ofNonresidues` projections and
`KeyDesc.decryptNat_ciphertext` under ordinary `module` import, `crtCombine_lt`, and
`toOuterMeasure_not_isNonresidueModPrime_le` on `(5, 13)`. -/
theorem ofNonresidues_and_bound_checks_65 (n : ℕ) (z_p z_q : ℕ) {r : ℕ} (hr : r.Coprime 65)
    (m : Bool) :
    (textbookPublicKey 5 13 z_p z_q).length ≤ 25 ∧
    (KeyDesc.ofNonresidues d65 (z_p := 3) (z_q := 2) (by decide) (by decide)).toModulusDesc = d65 ∧
    (KeyDesc.ofNonresidues d65 (z_p := 3) (z_q := 2) (by decide) (by decide)).z = 28 ∧
    decryptNat 5 13
      (ciphertext 65 (crtCombine 5 13 (3 % 5) 2 (BinaryGcd.modInv 5 13)) m r) = m ∧
    crtCombine 5 13 (z_p % 5) z_q (BinaryGcd.modInv 5 13) < 65 ∧
    (ProbComp.eval (sampleNonresidueModPrime n 5)).toOuterMeasure
      {a | isNonresidueModPrime 5 a = false} ≤ ((1 / 2 ^ (n + 1) : ℝ≥0) : ℝ≥0∞) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let k := KeyDesc.ofNonresidues d65 (z_p := 3) (z_q := 2) (by decide) (by decide)
  exact ⟨length_textbookPublicKey_le (B := 4) (by decide) (by decide) (by decide) (by decide)
      z_p z_q,
    by simp,
    (KeyDesc.ofNonresidues_z d65 _ _).trans crtCombine_5_13_eq_28,
    k.decryptNat_ciphertext hr m,
    crtCombine_lt (Nat.mod_lt _ (by decide)) (by decide) _ _,
    toOuterMeasure_not_isNonresidueModPrime_le (by decide) n⟩

/-! ### Single-bit and multi-bit textbook Goldwasser–Micali security clients -/

/-- `indcpa_textbookGoldwasserMicali` and `wordINDCPA_textbookGoldwasserMicali` yield single-bit
`INDCPA`, multi-bit `WordINDCPA`, and oracle-CPA security `WordINDCPAOracle` without any
Blum-modulus or ideal-key hypothesis. -/
theorem textbookINDCPA_and_wordINDCPA_and_oracle {gen : ℕ → ProbComp ModulusDesc}
    {sizeBound : ℕ → ℕ} (hbound : PolynomiallyBounded sizeBound)
    (hsize : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (hupper : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support,
      d.p.size ≤ sizeBound n ∧ d.q.size ≤ sizeBound n)
    (hQR : QuadraticResiduosityHard fun n => ProbComp.eval (gen n)) :
    INDCPA (textbookKeyGen gen) encrypt ∧
      WordINDCPA (textbookKeyGen gen) encryptWord ∧
      WordINDCPAOracle (textbookKeyGen gen) encryptWord := by
  have h1 := indcpa_textbookGoldwasserMicali hsize hQR
  have hw := wordINDCPA_textbookGoldwasserMicali hbound hsize hupper hQR
  exact ⟨h1, hw, hw.wordINDCPAOracle isPPTOn_encryptWord⟩

/-- Direct client of `isPPTOn_textbookKeyGen` and `INDCPA.wordINDCPA_bitwiseEncrypt`: when `gen` is
uniform strict PPT, `textbookKeyGen gen` is uniform strict PPT and `WordINDCPA` follows without an
separate `sizeBound` / `hupper` hypothesis. -/
theorem textbookWordINDCPA_of_isPPTOn {gen : ℕ → ProbComp ModulusDesc}
    (hgen : IsPPTOn encUnary encModulusDesc gen)
    (hsize : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (hQR : QuadraticResiduosityHard fun n => ProbComp.eval (gen n)) :
    IsPPTOn encUnary (encPair encBits encBits) (textbookKeyGen gen) ∧
      WordINDCPA (textbookKeyGen gen) encryptWord :=
  ⟨isPPTOn_textbookKeyGen hgen,
   (indcpa_textbookGoldwasserMicali hsize hQR).wordINDCPA_bitwiseEncrypt
     (isPPTOn_textbookKeyGen hgen) isPPTOn_encrypt⟩

/-! ### Unconditional joint satisfiability of `hbound`, `hsize`, and `hupper` via Bertrand -/

private theorem exists_bounded_modulusDesc (n : ℕ) :
    ∃ d : ModulusDesc,
      (n ≤ d.p.size ∧ n ≤ d.q.size) ∧
      (d.p.size ≤ n + 4 ∧ d.q.size ≤ n + 4) := by
  let B := max n 1
  have h2B_ge2 : 2 ≤ 2 ^ B := by
    have h1 : 1 ≤ B := le_max_right n 1
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) h1
  obtain ⟨p, hp, hp_gt, hp_le⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ B) (by positivity)
  obtain ⟨q, hq, hq_gt, hq_le⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ (B + 1)) (by positivity)
  have hp_lt_pow : p < 2 ^ (B + 2) := by
    calc p ≤ 2 * 2 ^ B := hp_le
      _ = 2 ^ (B + 1) := by ring
      _ < 2 ^ (B + 2) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)
  have hq_lt_pow : q < 2 ^ (B + 3) := by
    calc q ≤ 2 * 2 ^ (B + 1) := hq_le
      _ = 2 ^ (B + 2) := by ring
      _ < 2 ^ (B + 3) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)
  have hp_lt_q : p < q := by
    calc p ≤ 2 * 2 ^ B := hp_le
      _ = 2 ^ (B + 1) := by ring
      _ < q := hq_gt
  have hn_le_B : 2 ^ n ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) (le_max_left n 1)
  have hB_le : B ≤ n + 1 := max_le (Nat.le_add_right n 1) (Nat.le_add_left 1 n)
  refine ⟨⟨p, q, hp, hq, hp_lt_q.ne, by omega, by omega⟩,
    ⟨(Nat.lt_size.mpr (hn_le_B.trans hp_gt.le)).le,
     (Nat.lt_size.mpr (hn_le_B.trans (hp_gt.le.trans hp_lt_q.le))).le⟩,
    ⟨(Nat.size_le.mpr hp_lt_pow).trans (by omega),
     (Nat.size_le.mpr hq_lt_pow).trans (by omega)⟩⟩

private noncomputable def textbookBoundedWitnessGen (n : ℕ) : ProbComp ModulusDesc :=
  pure (exists_bounded_modulusDesc n).choose

/-- All modulus hypotheses (`hbound`, `hsize`, `hupper` with `sizeBound n = n + 4`) of
`indcpa_textbookGoldwasserMicali` and `wordINDCPA_textbookGoldwasserMicali` hold simultaneously on
`textbookBoundedWitnessGen`, leaving `QuadraticResiduosityHard` as the sole hypothesis. -/
theorem indcpa_and_wordINDCPA_textbookBoundedWitnessGen
    (hQR : QuadraticResiduosityHard fun n => ProbComp.eval (textbookBoundedWitnessGen n)) :
    INDCPA (textbookKeyGen textbookBoundedWitnessGen) encrypt ∧
      WordINDCPA (textbookKeyGen textbookBoundedWitnessGen) encryptWord := by
  have hbound : PolynomiallyBounded (fun n => n + 4) := by fun_prop
  have hsize : ∀ n, ∀ d ∈ (ProbComp.eval (textbookBoundedWitnessGen n)).support,
      n ≤ d.p.size ∧ n ≤ d.q.size := by
    intro n d hd
    simp only [textbookBoundedWitnessGen, ProbComp.eval_pure, PMF.support_pure,
      Set.mem_singleton_iff] at hd
    exact hd ▸ (exists_bounded_modulusDesc n).choose_spec.1
  have hupper : ∀ n, ∀ d ∈ (ProbComp.eval (textbookBoundedWitnessGen n)).support,
      d.p.size ≤ n + 4 ∧ d.q.size ≤ n + 4 := by
    intro n d hd
    simp only [textbookBoundedWitnessGen, ProbComp.eval_pure, PMF.support_pure,
      Set.mem_singleton_iff] at hd
    exact hd ▸ (exists_bounded_modulusDesc n).choose_spec.2
  exact ⟨indcpa_textbookGoldwasserMicali hsize hQR,
    wordINDCPA_textbookGoldwasserMicali hbound hsize hupper hQR⟩

end CslibFrontierTests.Crypto.GoldwasserMicaliTextbook
