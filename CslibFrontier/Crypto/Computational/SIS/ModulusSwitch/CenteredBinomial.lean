/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.ModulusSwitch.Failure
public import CslibFrontier.Crypto.Computational.SIS.ModuleEncryption.Sampling
public import CslibFrontier.Crypto.Computational.SIS.ModuleEncryption.Sampling.Concentration
public import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import Mathlib.Data.Nat.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-!
# Growing centered-binomial parameters for switched Module-LWE correctness

These original sufficient parameters concern correctness of the existing sampled encryption
experiment. Rank and degree both grow, the moduli have explicit polynomial bounds, and the
same sampled secret generates the key and decrypts the switched ciphertext. No small-secret
hardness assumption, security reduction, or complete native encryption certificate is claimed.

## Main definitions

* `moduleLWECBDRadius`: the target decoding radius.
* `moduleLWECBDWidth`: the width of a target modulus strictly above its decoding margin.

## Main results

* `computableInPolyTime_moduleLWECBDWidth`: the uniform unary parameter certificate.
* `moduleLWECBD_modulus_le`, `moduleLWECBD_sourceModulus_le`: cubic modulus bounds.
* `toOuterMeasure_moduleLWECBD_switch_failure_le`: the actual failure is at most
  `4 (2t+1) t exp(-t)` for rank and degree `t = l+1`.
* `negligible_moduleLWECBD_switch_failure`: negligible failure for every message family.

The native sampling clients use unary dimensions/widths, signed binary CBD samples and binary
uniform samples below the power-of-two modulus. The modular sampling identities are semantic;
native encryption, switched-decryption assembly and seed codecs remain separate (unswitched key
generation and decryption are certified in `SIS/ModuleEncryption/Native`).
-/

public section

namespace Cslib.Crypto

open Probability ProbComp
open scoped ENNReal NNReal

/-- Target radius for rank and degree `t`, CBD1 secrets and CBD(8t) errors with good radius 4t. -/
@[expose] def moduleLWECBDRadius (t : ℕ) : ℕ := (8 * t ^ 3 + t ^ 2 + 4 * t + 2) / 2

/-- Binary width chosen so that the target modulus `2^width` exceeds `4*radius+2`. -/
@[expose] def moduleLWECBDWidth (t : ℕ) : ℕ := Nat.size (4 * moduleLWECBDRadius t + 2)

open Turing.MultiTapeTM in
/-- The complete width schedule is computed uniformly from a unary dimension parameter. -/
@[fun_prop]
theorem computableInPolyTime_moduleLWECBDWidth :
    ComputableInPolyTime moduleLWECBDWidth encUnary encUnary := by
  unfold moduleLWECBDWidth moduleLWECBDRadius
  apply ComputableInPolyTime.binary_size.comp
  apply ComputableInPolyTime.unary_to_binary.comp
  fun_prop

/-- The chosen modulus meets the actual strict decoder margin. -/
theorem moduleLWECBD_margin (t : ℕ) :
    4 * moduleLWECBDRadius t + 2 < 2 ^ moduleLWECBDWidth t :=
  Nat.lt_size_self _

private theorem radius_lower (t : ℕ) :
    8 * t ^ 3 + t ^ 2 + 4 * t + 1 ≤ 2 * moduleLWECBDRadius t := by
  unfold moduleLWECBDRadius
  omega

private theorem radius_upper {t : ℕ} (ht : 0 < t) : moduleLWECBDRadius t ≤ 8 * t ^ 3 := by
  unfold moduleLWECBDRadius
  nlinarith [Nat.le_self_pow (by decide : 2 ≠ 0) t,
    Nat.pow_le_pow_right ht (by decide : 2 ≤ 3),
    Nat.div_mul_le_self (8 * t ^ 3 + t ^ 2 + 4 * t + 2) 2]

/-- The target modulus grows at most cubically as a number, not merely in bit length. -/
theorem moduleLWECBD_modulus_le {t : ℕ} (ht : 0 < t) :
    2 ^ moduleLWECBDWidth t ≤ 68 * t ^ 3 := by
  have hpos : 0 < moduleLWECBDWidth t := Nat.size_pos.mpr (by omega)
  have hpow : 2 ^ (moduleLWECBDWidth t - 1) ≤ 4 * moduleLWECBDRadius t + 2 :=
    Nat.lt_size.mp (Nat.sub_lt hpos Nat.one_pos)
  rw [← Nat.sub_add_cancel hpos, pow_succ]
  nlinarith [radius_upper ht, Nat.one_le_pow 3 t ht]

/-- The source modulus has the same polynomial number-size bound. -/
theorem moduleLWECBD_sourceModulus_le {t : ℕ} (ht : 0 < t) :
    2 ^ (moduleLWECBDWidth t + 1) ≤ 136 * t ^ 3 := by
  rw [pow_succ]
  nlinarith [moduleLWECBD_modulus_le ht]

/-- Even the full CBD(8t) support lies strictly inside the centered source interval. -/
theorem moduleLWECBD_noWrap (t : ℕ) :
    2 * (8 * t) < 2 ^ (moduleLWECBDWidth t + 1) := by
  rw [pow_succ]
  nlinarith [moduleLWECBD_margin t, radius_lower t, Nat.zero_le (t ^ 3), Nat.zero_le (t ^ 2)]

private theorem family_budget (t : ℕ) :
    ((2 ^ moduleLWECBDWidth t : ℕ) : ℚ) / 2 ^ (moduleLWECBDWidth t + 1) *
        (t * t * (4 * t) * 1 + t * t * (4 * t) * 1 + 4 * t : ℕ) +
      (1 + t * t * 1) / 2 +
      |((2 ^ moduleLWECBDWidth t : ℕ) : ℚ) / 2 ^ (moduleLWECBDWidth t + 1) *
        (2 ^ (moduleLWECBDWidth t + 1) / 2 : ℕ) -
        (2 ^ moduleLWECBDWidth t / 2 : ℕ)| ≤ moduleLWECBDRadius t := by
  have hw : 0 < moduleLWECBDWidth t := Nat.size_pos.mpr (by omega)
  rw [show ((2 ^ moduleLWECBDWidth t : ℕ) : ℚ) / 2 ^ (moduleLWECBDWidth t + 1) = 1 / 2 by
      push_cast
      rw [pow_succ]
      field_simp,
    Nat.cast_div_charZero (dvd_pow_self 2 (by omega : moduleLWECBDWidth t + 1 ≠ 0)),
    Nat.cast_div_charZero (dvd_pow_self 2 hw.ne')]
  push_cast
  rw [show (1 / 2 : ℚ) * (2 ^ (moduleLWECBDWidth t + 1) / 2) - 2 ^ moduleLWECBDWidth t / 2 = 0 by
    rw [pow_succ]; ring, abs_zero, add_zero]
  nlinarith [show (8 : ℚ) * t ^ 3 + t ^ 2 + 4 * t + 1 ≤ 2 * moduleLWECBDRadius t by
    exact_mod_cast radius_lower t]

/-- In the actual retained-secret experiment, growing rank and degree cost the full
`(2*t+1)*t` coefficient union factor. This is a correctness bound for every message. -/
theorem toOuterMeasure_moduleLWECBD_switch_failure_le (l : ℕ) (m : Fin (l + 1) → Bool) :
    let t := l + 1
    let w := moduleLWECBDWidth t
    let noise := PMF.pi (fun _ : Fin t => LWE.noiseLaw (w + 1) (8 * t))
    let secrets := PMF.pi (fun _ : Fin t =>
      PMF.pi (fun _ : Fin t => LWE.noiseLaw (w + 1) 1))
    (do
      let s ← secrets
      let view ← encryptionViewOfKeyLaw
        (moduleLWEPublicKeyLaw t t (2 ^ (w + 1)) noise (PMF.pure s)) noise m secrets
      pure (s, view)).toOuterMeasure
        {(s, _, ct) | moduleLWEDecrypt
          (fun j i => (SIS.liftCentered (s j) i : ZMod (2 ^ w)))
          (moduleLWEModulusSwitch (2 ^ w) ct) ≠ m} ≤
      ENNReal.ofReal (4 * (2 * (t : ℝ) + 1) * t * Real.exp (-(t : ℝ))) := by
  dsimp only
  let t := l + 1
  let w := moduleLWECBDWidth t
  let noise := PMF.pi (fun _ : Fin t => LWE.noiseLaw (w + 1) (8 * t))
  let secrets := PMF.pi (fun _ : Fin t => PMF.pi (fun _ : Fin t => LWE.noiseLaw (w + 1) 1))
  have hs : ∀ s ∈ secrets.support, ModuleSIS.inInfNormBound 1 s := fun _ =>
    moduleLWECenteredBinomial_inInfNormBound (by
      have := moduleLWECBD_noWrap t
      dsimp only [t, w] at *
      omega)
  have hn := toOuterMeasure_moduleLWECBD_noise_tail_le (n := t) (B := 4 * t)
    (by dsimp only [t]; positivity : 0 < 8 * t) (moduleLWECBD_noWrap t)
  rw [show -((4 * t : ℕ) : ℝ) ^ 2 / (2 * (8 * t : ℕ)) = -(t : ℝ) by
    dsimp only [t]
    push_cast
    field_simp
    ring] at hn
  refine (toOuterMeasure_moduleLWEModulusSwitch_failure_le
    (k := t) (n := t) (q := 2 ^ (w + 1)) (p := 2 ^ w)
    (Bs := 1) (Br := 1) (Be := 4 * t) (Bp := moduleLWECBDRadius t)
    (moduleLWECBD_margin t) noise m secrets secrets hs hs
    (by simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, w] using family_budget t)).trans
    ((mul_le_mul' le_rfl hn).trans_eq ?_)
  change (2 * (t : ℝ≥0∞) + 1) * (t * ENNReal.ofReal (4 * Real.exp (-(t : ℝ)))) =
    ENNReal.ofReal (4 * (2 * (t : ℝ) + 1) * t * Real.exp (-(t : ℝ)))
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * (2 * (t : ℝ) + 1) * t),
    ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * (2 * (t : ℝ) + 1))]
  simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
    ENNReal.ofReal_add (by positivity : 0 ≤ 2 * (t : ℝ)) (by norm_num : (0 : ℝ) ≤ 1),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat, ENNReal.ofReal_one]
  ring

/-- The actual switched-decryption failure is negligible for every message family. This
is correctness of the supplied small-secret laws, with no hardness or security conclusion. -/
theorem negligible_moduleLWECBD_switch_failure (m : (l : ℕ) → Fin (l + 1) → Bool) :
    Negligible (fun l =>
      let t := l + 1
      let w := moduleLWECBDWidth t
      let noise := PMF.pi (fun _ : Fin t => LWE.noiseLaw (w + 1) (8 * t))
      let secrets := PMF.pi (fun _ : Fin t =>
        PMF.pi (fun _ : Fin t => LWE.noiseLaw (w + 1) 1))
      ((do
        let s ← secrets
        let view ← encryptionViewOfKeyLaw
          (moduleLWEPublicKeyLaw t t (2 ^ (w + 1)) noise (PMF.pure s)) noise (m l) secrets
        pure (s, view)).toOuterMeasure
          {(s, _, ct) | moduleLWEDecrypt
            (fun j i => (SIS.liftCentered (s j) i : ZMod (2 ^ w)))
            (moduleLWEModulusSwitch (2 ^ w) ct) ≠ m l}).toNNReal) := by
  let ratio : ℝ≥0 := ⟨Real.exp (-1), (Real.exp_pos _).le⟩
  have hratio : ratio < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hpoly : PolynomiallyBounded (fun l : ℕ => 4 * (2 * (l + 1) + 1) * (l + 1)) := by fun_prop
  refine negligible_of_le (((negligible_geometric hratio).shift 1).polynomiallyBounded_mul hpoly)
    fun l => NNReal.coe_le_coe.mp ?_
  change _ ≤ ((4 * (2 * (l + 1) + 1) * (l + 1) : ℕ) : ℝ) * Real.exp (-1) ^ (l + 1)
  refine ((ENNReal.le_ofReal_iff_toReal_le (PMF.toOuterMeasure_ne_top _ _) (by positivity)).mp
    (toOuterMeasure_moduleLWECBD_switch_failure_le l (m l))).trans_eq ?_
  push_cast
  rw [← Real.exp_nat_mul]
  exact congrArg₂ (· * ·) (by ring) (congrArg Real.exp (by push_cast; ring))

end Cslib.Crypto
