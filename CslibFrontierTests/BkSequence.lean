/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Foundations.Combinatorics.Additive.BkSequence
import CslibFrontier.Computability.Complexity.BkSequencePolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Client tests for Sergeev's explicit finite `B_k`-sequence

Exercises `Cslib.IsBkSet`, `Cslib.IsBkSequence`, `Cslib.dlogFiveModTwoPow`,
`Cslib.sergeevBkSequence`, and `Cslib.Complexity.computableInPolyTime_sergeevBkSequence` under
ordinary module imports, checking concrete evaluations, the `ZMod N` counting lower bound, boundary
cases, and a negative witness showing `{0, 1, 2}` is not a Sidon (`B_2`) set.
-/

set_option linter.privateModule false

open Cslib Cslib.Complexity Turing.MultiTapeTM

-- First odd primes and concrete `H[3, 2]` evaluation:
-- `p₁ = 3, p₂ = 5, p₃ = 7`, `r = 1 + ⌈log₂ 49⌉ = 7`, `2^r = 128`, `2^(r - 2) = 32`,
-- `3 ≡ -5^3`, `5 ≡ +5^1`, `7 ≡ -5^10 (mod 128)`.
private theorem firstOddPrimes_three : firstOddPrimes 3 = [3, 5, 7] := by decide

private theorem sergeevModulusExp_three_two : sergeevModulusExp 3 2 = 7 := by decide

private theorem sergeevBkSequence_three_two : sergeevBkSequence 3 2 = [3, 1, 10] := by decide

-- Concrete `H[4, 2]` evaluation (`p = [3, 5, 7, 11]`, `11^2 = 121`, `r = 1 + 7 = 8`,
-- `2^r = 256`, `2^(r - 2) = 64`):
-- `3 ≡ -5^35`, `5 ≡ +5^1`, `7 ≡ -5^10`, `11 ≡ -5^21 (mod 256)`.
private theorem sergeevModulusExp_four_two : sergeevModulusExp 4 2 = 8 := by decide

private theorem dlogFiveModTwoPow_eight_eleven : dlogFiveModTwoPow 8 11 = 21 := by decide

private theorem sergeevBkSequence_four_two : sergeevBkSequence 4 2 = [35, 1, 10, 21] := by decide

-- Boundary witness at `n = 0`: empty `B_k`-sequence of length `0`.
private theorem sergeevBkSequence_zero (k : ℕ) :
    sergeevBkSequence 0 k = [] ∧ IsBkSequence (k + 1) (sergeevBkSequence 0 (k + 1)) :=
  ⟨by simp [sergeevBkSequence, firstOddPrimes], isBkSequence_sergeevBkSequence 0 (Nat.succ_pos k)⟩

-- Specializing `IsBkSet.choose_le_card` to `ZMod N` yields `(#B + k - 1).choose k ≤ N` directly.
private theorem choose_le_zmod_of_sergeev (n k : ℕ) (hk : 1 ≤ k) :
    (n + k - 1).choose k ≤ 2 ^ (sergeevModulusExp n k - 2) := by
  let N := 2 ^ (sergeevModulusExp n k - 2)
  let L := (sergeevBkSequence n k).map (Nat.cast : ℕ → ZMod N)
  have : NeZero N := ⟨(Nat.two_pow_pos _).ne'⟩
  have hbk := isBkSequence_map_zmod_sergeevBkSequence n hk
  have hset : IsBkSet k (L.toFinset : Set (ZMod N)) := by
    intro s t hs ht hsc htc hsum
    exact hbk.2 (fun a ha => List.mem_toFinset.mp (hs a ha))
      (fun b hb => List.mem_toFinset.mp (ht b hb)) hsc htc hsum
  have hcard : L.toFinset.card = n := by
    rw [List.toFinset_card_of_nodup hbk.1, List.length_map, length_sergeevBkSequence]
  simpa only [hcard, ZMod.card] using hset.choose_le_card

-- Negative witness: `{0, 1, 2} ⊆ ℕ` is NOT a `B_2`-set because `0 + 2 = 1 + 1` while
-- `{0, 2} ≠ {1, 1}` as multisets.
private theorem not_isBkSet_two_zero_one_two :
    ¬ IsBkSet 2 ({0, 1, 2} : Set ℕ) := by
  intro h
  have heq : ({0, 2} : Multiset ℕ) = ({1, 1} : Multiset ℕ) := by
    apply h
    · intro a ha
      rcases Multiset.mem_cons.mp ha with rfl | ha'
      · exact Set.mem_insert 0 _
      · rw [Multiset.mem_singleton.mp ha']
        exact Set.mem_insert_of_mem 0 (Set.mem_insert_of_mem 1 (Set.mem_singleton 2))
    · intro b hb
      rcases Multiset.mem_cons.mp hb with rfl | hb'
      · exact Set.mem_insert_of_mem 0 (Set.mem_insert 1 _)
      · rw [Multiset.mem_singleton.mp hb']
        exact Set.mem_insert_of_mem 0 (Set.mem_insert 1 _)
    · rfl
    · rfl
    · rfl
  have h0 : (0 : ℕ) ∈ ({1, 1} : Multiset ℕ) := heq ▸ Multiset.mem_cons_self 0 _
  revert h0
  decide

-- Client composition of the polynomial-time constructibility theorem: fixing `k = 2` produces
-- explicit Sidon sequences of size `n` in time `n ^ O(1)` from unary `n` via `fun_prop`.
private theorem computableInPolyTime_sergeevSidon :
    ComputableInPolyTime (fun n : ℕ => sergeevBkSequence n 2) encUnary (encList encNat) := by
  fun_prop
