/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Paillier.Statistical
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Tactic.NormNum.Prime

/-!
# Statistical Paillier homomorphism clients and fixed-ciphertext rerandomization

The `N = 143`, `n = 4` client uses the nonvacuous error `5 / 8` and postprocesses ciphertexts to
natural numbers. At the smaller valid balanced modulus `N = 35`, `n = 0`, exact rerandomization
fails: a fresh encryption of zero assigns mass `23 / 64` to `encNat 1`, whereas multiplying by
the supported ciphertext `encNat 18` assigns mass `1 / 32`. The finite fibers below are computed
in the kernel from the actual encryption program, including its nonunit fallback.
-/

namespace CslibFrontierTests.Crypto.PaillierStatistical

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Paillier BalancedModulus
open Turing.MultiTapeTM
open scoped ENNReal

private def d143 : Desc :=
  ⟨(11, 13), ⟨by norm_num, by norm_num, by decide, by norm_num, by norm_num, by decide⟩⟩

-- The bound remains useful after an arbitrary-output observation, including when the plaintext
-- sum wraps modulo N. Neither the theorem nor this client replaces the implemented sampler.
example :
    CloseTo
      ((ProbComp.eval (do
        let ct₁ ← encrypt 4 (encNat 143) 100
        let ct₂ ← encrypt 4 (encNat 143) 50
        return addCiphertexts (encNat 143) ct₁ ct₂)).map (fun ct => ofBits ct % 7))
      ((ProbComp.eval (encrypt 4 (encNat 143) 150)).map (fun ct => ofBits ct % 7)) (5 / 8) := by
  have h := (closeTo_addCiphertexts d143 4 100 50 ⟨by decide, by decide⟩).map
    (fun ct => ofBits ct % 7)
  have herror : (10 : ℝ≥0∞) / 2 ^ 4 = 5 / 8 := by
    norm_num
    rw [ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  rw [show d143.modulus = 143 from rfl, herror] at h
  exact h

private def d35 : Desc :=
  ⟨(5, 7), ⟨by norm_num, by norm_num, by decide, by norm_num, by norm_num, by decide⟩⟩

private def seedCiphertext (r : Fin 64) : List Bool :=
  encNat (ciphertext 35 0 (unitOrOne 35 (r.val % 35)))

private theorem eval_encrypt35 :
    ProbComp.eval (encrypt 0 (encNat 35) 0) =
      (PMF.uniformOfFintype (Fin 64)).map seedCiphertext := by
  simp only [encrypt, ofBits_encNat, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_sampleModNat, PMF.bind_map]
  change (PMF.uniformOfFintype (Fin 64)).bind (fun r => PMF.pure (seedCiphertext r)) = _
  exact PMF.bind_pure_comp _ _

private theorem fresh_fiber : Nat.card {r : Fin 64 // seedCiphertext r = encNat 1} = 23 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem product_fiber :
    Nat.card {r : Fin 64 //
      addCiphertexts (encNat 35) (encNat 18) (seedCiphertext r) = encNat 1} = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem fresh_mass :
    (ProbComp.eval (encrypt 0 (encNat 35) 0) (encNat 1)).toReal = 23 / 64 := by
  rw [eval_encrypt35, PMF.uniformOfFintype_map_apply, fresh_fiber]
  norm_num [ENNReal.toReal_div]

private theorem product_mass :
    (((ProbComp.eval (encrypt 0 (encNat 35) 0)).map
      (addCiphertexts (encNat 35) (encNat 18))) (encNat 1)).toReal = 1 / 32 := by
  rw [eval_encrypt35, PMF.map_comp, PMF.uniformOfFintype_map_apply]
  change ((Nat.card {r : Fin 64 //
      addCiphertexts (encNat 35) (encNat 18) (seedCiphertext r) = encNat 1} : ℝ≥0∞) /
    Fintype.card (Fin 64)).toReal = _
  rw [product_fiber]
  norm_num [ENNReal.toReal_div]

-- Exact fixed-ciphertext rerandomization fails for a valid balanced modulus and a ciphertext
-- that the word encryptor actually produces.
/-- A supported ciphertext can change the fresh word-encryption law under multiplication. -/
public theorem exists_fixed_ciphertext_law_ne :
    ∃ d : Desc, ∃ ct₁ ∈ (ProbComp.eval (encrypt 0 (encNat d.modulus) 0)).support,
    (ProbComp.eval (encrypt 0 (encNat d.modulus) 0)).map
      (addCiphertexts (encNat d.modulus) ct₁) ≠
        ProbComp.eval (encrypt 0 (encNat d.modulus) (0 + 0)) := by
  refine ⟨d35, encNat 18, ?_, ?_⟩
  · change encNat 18 ∈ (ProbComp.eval (encrypt 0 (encNat 35) 0)).support
    rw [eval_encrypt35, PMF.mem_support_map_iff]
    exact ⟨⟨2, by decide⟩, PMF.mem_support_uniformOfFintype _, by decide⟩
  · change (ProbComp.eval (encrypt 0 (encNat 35) 0)).map
      (addCiphertexts (encNat 35) (encNat 18)) ≠ ProbComp.eval (encrypt 0 (encNat 35) 0)
    intro h
    have hm := congrArg (fun μ : PMF (List Bool) => (μ (encNat 1)).toReal) h
    rw [product_mass, fresh_mass] at hm
    norm_num at hm

end CslibFrontierTests.Crypto.PaillierStatistical
