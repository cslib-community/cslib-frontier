/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.LetterSubst
import CslibFrontier.Foundations.Data.MvPolynomial.Substitution
import CslibFrontier.Foundations.Data.Nat.Power

/-! Tests of the end of the proof of Lemma K.3 and of Theorem K.7 of [AnthropicVPVNP2026] as a
client: naming the letters `0` and `1` of the alphabet `Fin 3` by bits, the value of a polynomial
at the code of a word of bits after it, the use in the proof of Lemma K.3, and the transport of a
power bound in the proof of Theorem K.7. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationLetterSubst

open MvPolynomial Cslib.Circuits.Arithmetic Cslib.Circuits.Arithmetic.Separation.Tape

/-- The bits `false` and `true` as the letters `0` and `1` of `Fin 3`; the letter `2` is unused. -/
private def bit : Bool → Fin 3 := fun b => if b then 1 else 0

private theorem bit_injective : Function.Injective bit := by decide

/-- The letter `1` at place `0` becomes the bit `true` at place `0`. -/
example : letterSubst ℚ bit 3 (0, some 1) = X (0, some true) :=
  letterSubst_map bit_injective 0 (some true)

/-- The unused letter `2` becomes `0`. -/
example : letterSubst ℚ bit 3 (1, some 2) = 0 :=
  letterSubst_of_notMem_range (by rintro ⟨_ | _ | _, h⟩ <;> simp [bit] at h) 1

/-- The product of the three set bits of the code of the word `[1, 0]` is `1` at the code of the
word of bits `[true, false]` after the substitution. -/
example : eval (fun b => if wordCode 3 [true, false] b then 1 else 0)
    (aeval (letterSubst ℚ bit 3) (X (0, some 1) * X (1, some 0) * X (2, none) :
      MvPolynomial (Fin 3 × Option (Fin 3)) ℚ)) = 1 := by
  rw [eval_aeval_letterSubst bit_injective]
  simp [bit, wordCode]

/-- An affine polynomial stays affine under the substitution. -/
example : IsAffine (aeval (letterSubst ℚ bit 3)
    (C 2 * X (0, some 1) + C 5 : MvPolynomial (Fin 3 × Option (Fin 3)) ℚ)) :=
  IsAffine.aeval (.inr ⟨_, 2, 5, rfl⟩) (isAffine_letterSubst bit 3)

/-- The use in the proof of Lemma K.3: after naming two letters by bits, an affine projection
`aeval Mat G` stays an affine projection, its total degree does not grow, and its value at the code
of a word of bits is its former value at the code of the word of letters. -/
example {Γ : Type} [DecidableEq Γ] {m n : ℕ} (bt : Bool → Γ) (hb : Function.Injective bt)
    (Mat : Fin m → MvPolynomial (Fin n × Option Γ) ℚ) (hMat : ∀ q, IsAffine (Mat q))
    (G : MvPolynomial (Fin m) ℚ) (w : List Bool) :
    let Mat' := fun q => aeval (letterSubst ℚ bt n) (Mat q)
    (∀ q, IsAffine (Mat' q)) ∧ (aeval Mat' G).totalDegree ≤ (aeval Mat G).totalDegree ∧
      eval (fun b => if wordCode n w b then 1 else 0) (aeval Mat' G) =
        eval (fun b => if wordCode n (w.map bt) b then 1 else 0) (aeval Mat G) := by
  intro Mat'
  have h : aeval Mat' G = aeval (letterSubst ℚ bt n) (aeval Mat G) :=
    (comp_aeval_apply Mat (aeval (letterSubst ℚ bt n)) G).symm
  refine ⟨fun q => (hMat q).aeval (isAffine_letterSubst bt n), ?_, ?_⟩
  · exact h ▸ totalDegree_aeval_le (fun i => (isAffine_letterSubst bt n i).totalDegree_le) _
  · rw [h, eval_aeval_letterSubst hb]

/-- The transport at `x = 2`, `y = 3`, `v = 9`, `a = b = E = 1`: `3 ^ 2 ≤ 9` and `2 ^ 2 ≤ 9`
give `2 ^ 2 ≤ 9`. -/
example : 2 ^ (1 * (1 + 1)) ≤ 9 :=
  Nat.pow_mul_add_one_le_of_pow_le (y := 3) one_ne_zero (by norm_num) (by norm_num) (by norm_num)

/-- The use in the proof of Theorem K.7, with `lg n = Nat.log 2 n + 1`: for `v ≤ m ≤ v ^ b`, a
polylogarithmic bound at `m` gives one at `v`. -/
example {v m a b E : ℕ} (hb : b ≠ 0) (hvm : v ≤ m) (hmv : m ≤ v ^ b)
    (hm : (Nat.log 2 m + 1) ^ (2 * b * E * a) ≤ m) (hv : (Nat.log 2 v + 1) ^ (2 * E) ≤ v) :
    (Nat.log 2 v + 1) ^ (E * (a + 1)) ≤ v :=
  Nat.pow_mul_add_one_le_of_pow_le hb (Nat.add_le_add_right (Nat.log_mono_right hvm) 1)
    (hm.trans hmv) hv

end CslibFrontierTests.SeparationLetterSubst
