/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.PerfectSecrecy.ShannonCiphers
import CslibFrontier.Probability.PMF.Map
import Mathlib.Data.ZMod.Defs

/-!
# The example ciphers of Boneh–Shoup §2.1: checked instances

Checks for `CslibFrontier.Crypto.Protocols.PerfectSecrecy.ShannonCiphers`, the example ciphers of
[BonehShoup2023] §2.1. The file is a `module` client with ordinary imports.

* The additive one-time pad over `ZMod 6` is perfectly secure, both through the uniform ciphertext
  law and through the book's route, `N_c = 1` with the key `-m + c`.
* The variable-length one-time pad with two key bits separates a 1-bit and a 2-bit message, and
  gives a 1-bit ciphertext mass `1/2` under a 1-bit message and `0` under a 2-bit message, the two
  numbers of Example 2.5. With no key bits it is perfectly secure, so `0 < L` is needed.
* The substitution cipher on two symbols of a three-letter alphabet is not perfectly secure. On one
  symbol of `Bool` it is, so `2 ≤ L` is needed.
-/

namespace CslibFrontierTests.Crypto.PerfectSecrecyCiphers

open Cslib Cslib.Probability.PMF Cslib.Crypto.Protocols.PerfectSecrecy

/-! ### The additive one-time pad -/

/-- The additive one-time pad over `ZMod 6`, the book's case `n = 6`, is perfectly secret. -/
public theorem additiveOTP_zmod_six_perfectlySecret : (additiveOTP (ZMod 6)).PerfectlySecret :=
  additiveOTP_perfectlySecret _

/-- The book's proof of Example 2.7: each message and ciphertext have exactly one key, `-m + c`. -/
example : (additiveOTP (ZMod 6)).CiphertextIndist :=
  EncScheme.ciphertextIndist_ofPure_uniformOfFintype_of_existsUnique _ _ _ fun m c =>
    ⟨-m + c, by simp, fun k hk => by rw [← hk]; simp⟩

/-! ### The variable-length one-time pad -/

/-- With two key bits, a 1-bit message and a 2-bit message have different ciphertext laws. -/
example (b b' : Bool) :
    (variableLengthOTP 2).ciphertextDist ⟨[b], by simp⟩ ≠
      (variableLengthOTP 2).ciphertextDist ⟨[b, b'], by simp⟩ := by
  rw [Ne, variableLengthOTP_ciphertextDist_eq_iff]
  simp

/-- The book's first number: a 1-bit ciphertext has probability `1/2` under a 1-bit message. -/
example (b c : Bool) :
    (variableLengthOTP 2).ciphertextDist ⟨[b], by simp⟩ ⟨[c], by simp⟩ = 1 / 2 := by
  rw [← map_apply_of_injective _ Subtype.val_injective, variableLengthOTP_ciphertextDist_map_val,
    List.length_singleton, BitString.uniformList_succ, BitString.uniformList_zero]
  simp only [PMF.pure_map]
  change ((uniformOfFintype Bool).bind (PMF.pure ∘ fun bit => [bit])) [c] = 1 / 2
  rw [PMF.bind_pure_comp, map_apply_of_injective _ (fun _ _ h => List.singleton_injective h),
    uniformOfFintype_apply, Fintype.card_bool, one_div, Nat.cast_ofNat]

/-- The book's second number: a 1-bit ciphertext has probability `0` under a 2-bit message. -/
example (b b' c : Bool) :
    (variableLengthOTP 2).ciphertextDist ⟨[b, b'], by simp⟩ ⟨[c], by simp⟩ = 0 :=
  variableLengthOTP_ciphertextDist_apply_of_length_ne 2 (by simp)

/-- With no key bits the only message is the empty word, and the cipher is perfectly secure. -/
example : (variableLengthOTP 0).CiphertextIndist :=
  (variableLengthOTP_ciphertextIndist_iff 0).mpr rfl

/-! ### The substitution cipher -/

/-- On words of two symbols over a three-letter alphabet, the substitution cipher is not perfectly
secure. -/
example : ¬ (substitutionCipher (Fin 3) 2).CiphertextIndist :=
  not_ciphertextIndist_substitutionCipher le_rfl

/-- On words of one symbol over `Bool` the substitution cipher is perfectly secure, through the
counting criterion with `N_c = 1`: the hypothesis `2 ≤ L` cannot be dropped. -/
example : (substitutionCipher Bool 1).CiphertextIndist :=
  (EncScheme.ciphertextIndist_ofPure_uniformOfFintype_iff _ _ _).mpr fun c => ⟨1, fun m => by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; revert m c; decide⟩

end CslibFrontierTests.Crypto.PerfectSecrecyCiphers
