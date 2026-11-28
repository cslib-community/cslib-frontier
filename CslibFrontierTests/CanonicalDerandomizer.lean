/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.BPP.Derandomization.CanonicalDerandomizer
import CslibFrontier.Computability.Complexity.Classes.BPP.Derandomization.GeneralTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp

/-! Checked instances of the generator records of Goldreich's Definition 8.14 and Arora and
Barak's Definition 16.2: the identity map on seeds satisfies both records (it has no stretch, and
its output is exactly uniform), so neither record is vacuous. The growth hypothesis of the
conditional forms of Lemma 16.4 and Proposition 8.15 holds for the stretches `m` and `2 ^ m`, and
the conditional form of Lemma 16.4 applies to the identity map. -/

set_option linter.privateModule false

namespace CslibFrontierTests.CanonicalDerandomizer

open Cslib Cslib.Complexity Cslib.Crypto.PRG Turing.MultiTapeTM Filter

/-- The identity map on seeds, restricted to seeds of `k` bits, is the identity. -/
theorem wordFamily_id (k : ℕ) (z : BitString k) : wordFamily (fun z => z) (fun k => k) k z = z := by
  funext i
  simp [wordFamily]

/-- Every test has advantage `0` against the identity generator. -/
theorem advantage_id (k : ℕ) (test : BitString k → Bool) :
    (wordFamily (fun z => z) (fun k => k) k).advantage (fun y => PMF.pure (test y)) = 0 := by
  rw [Generator.advantage_pure_eq]
  simp only [wordFamily_id, sub_self, abs_zero]

/-- The identity map is computable within time and space `O(T |z|)` for every `T k ≥ k`. -/
theorem computableInO_id (T : ℕ → ℕ) (hT : ∀ k, k ≤ T k) :
    ComputableInO (fun z : List Bool => z) encBits encBits (fun z => T z.length)
      fun z => T z.length :=
  ComputableInO.id'.mono_le (fun z => by simpa using hT z.length) fun z => by
    simpa using hT z.length

/-- The identity map is a canonical derandomizer of stretch `ℓ(k) = k`. -/
example : CanonicalDerandomizer (fun z => z) fun k => k where
  monotone := monotone_id
  length_eq _ := rfl
  time := ⟨1, computableInO_id (fun k => (2 ^ k * (k + 1)) ^ 1) fun k => by
    rw [pow_one]
    exact Nat.lt_two_pow_self.le.trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos k))⟩
  fools k adversary := by
    rintro ⟨test, -, rfl⟩
    rw [advantage_id]
    norm_num

/-- The identity map is a `k`-pseudorandom generator in the sense of Arora and Barak. -/
theorem exponentialTimePRG_id : ExponentialTimePRG (fun z => z) fun k => k where
  monotone := monotone_id
  length_eq _ := rfl
  time := ⟨1, computableInO_id (fun k => 2 ^ (1 * k)) fun k => by
    rw [one_mul]
    exact Nat.lt_two_pow_self.le⟩
  pseudorandom k adversary := by
    rintro ⟨test, -, rfl⟩
    rw [advantage_id]
    norm_num

/-- Exercise 8.18 bounds the stretch of every canonical derandomizer, here `k ≤ 2 ^ (k + 1) + 1`. -/
example (hG : CanonicalDerandomizer (fun z => z) fun k => k) (k : ℕ) : k ≤ 2 ^ (k + 1) + 1 :=
  hG.le_two_pow k

/-- The growth condition `S(O(m)) ≥ c S(m)` holds for the polynomial stretch `S(m) = m`. -/
example : ∀ c : ℕ, ∃ d : ℕ, ∀ m, c * m ≤ d * (m + 1) :=
  fun c => ⟨c, fun m => Nat.mul_le_mul_left c (Nat.le_succ m)⟩

/-- The growth condition `S(O(m)) ≥ c S(m)` holds for the exponential stretch `S(m) = 2 ^ m`. -/
example : ∀ c : ℕ, ∃ d : ℕ, ∀ m, c * 2 ^ m ≤ 2 ^ (d * (m + 1)) := fun c => ⟨c + 1, fun m => by
  calc c * 2 ^ m ≤ 2 ^ c * 2 ^ m := Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
    _ = 2 ^ (c + m) := (pow_add 2 c m).symm
    _ ≤ 2 ^ ((c + 1) * (m + 1)) := Nat.pow_le_pow_right two_pos (by nlinarith)⟩

/-- The conditional form of Lemma 16.4 applies to the identity map with `S(m) = m` and seeds of
`ℓ(n) = n` bits: `BPTIME(n) ⊆ DTIME(2 ^ O(n))`. -/
example {α : Type} (enc : α ↪ List Bool) :
    BPTIME enc (fun n => n) ⊆ ⋃ c : ℕ, DTIME enc fun n => 2 ^ (c * n) :=
  BPTIME_subset_DTIME_of_exponentialTimePRG_of_growth (ℓ := fun n => n) exponentialTimePRG_id
    (fun c => ⟨c, fun m => Nat.mul_le_mul_left c (Nat.le_succ m)⟩) (by fun_prop) (fun _ => le_rfl)
    enc

end CslibFrontierTests.CanonicalDerandomizer
