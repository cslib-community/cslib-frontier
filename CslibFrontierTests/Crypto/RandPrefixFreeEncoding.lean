/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Primitives.PRF.RandPrefixFreeEncoding
import CslibFrontier.Foundations.Data.List.ModifyLast
import Mathlib.Probability.ProbabilityMassFunction.Basic

public section

/-!
# Tests for randomized prefix-free encodings

Checks the book's corollaries through the library theorems, pins `cmacRpf` to the two output lines
of Boneh–Shoup §6.10 on concrete inputs, and gives a counterexample for each hypothesis the library
adds: non-empty messages for the one-key encoding, `0 < n` and `1 ≤ ℓ` for CMAC, and two
independent CMAC keys.
-/

namespace Cslib.Tests.RandPrefixFreeEncoding

open Cslib Cslib.Crypto Cslib.Crypto.PRF Cslib.Probability
open scoped ENNReal

/-! ### Corollaries -/

/-- On `n`-bit blocks the one-key encoding is `2⁻ⁿ`-prefix-free (§6.7, `1/|X|` with `|X| = 2ⁿ`). -/
example (n : ℕ) :
    IsRandPrefixFreeEncoding (PMF.uniformOfFintype (BitString n))
      (fun k (m : {m : List (BitString n) // m ≠ []}) => m.1.modifyLast (· + k))
      ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  simpa [BitString.card] using isRandPrefixFreeEncoding_modifyLast_add (BitString n)

/-- The one-key encoding restricted to the book's domain `X^{≤ℓ}_{>0}`, through `comp_injective`. -/
example (X : Type*) [Fintype X] [Nonempty X] [AddGroup X] (ℓ : ℕ) :
    IsRandPrefixFreeEncoding (PMF.uniformOfFintype X)
      (fun k (m : {m : List X // m ≠ [] ∧ m.length ≤ ℓ}) => m.1.modifyLast (· + k))
      (Fintype.card X : ℝ≥0∞)⁻¹ :=
  (isRandPrefixFreeEncoding_modifyLast_add X).comp_injective
    (e := fun m => ⟨m.1, m.2.1⟩) fun _ _ h => Subtype.ext (by simpa using congrArg Subtype.val h)

/-- CMAC's encoding restricted to the book's domain `{0,1}^{≤nℓ}`, with at most `ℓ` blocks. -/
example {n ℓ : ℕ} (hn : 0 < n) (hℓ : 1 ≤ ℓ) :
    IsRandPrefixFreeEncoding (PMF.uniformOfFintype (BitString n × BitString n))
        (fun k (m : {m : List Bool // m.length ≤ n * ℓ}) => cmacRpf n k m.1) ((2 : ℝ≥0∞) ^ n)⁻¹ ∧
      ∀ k (m : {m : List Bool // m.length ≤ n * ℓ}), (cmacRpf n k m.1).length ≤ ℓ :=
  ⟨(isRandPrefixFreeEncoding_cmacRpf hn).comp_injective Subtype.val_injective,
    fun k m => length_cmacRpf_le hn hℓ k m.2⟩

/-! ### Concrete values -/

/-- `+` on `BitString 2` is bitwise XOR: `01 + 11 = 10`. -/
example : (![false, true] + ![true, true] : BitString 2) = ![true, false] := by decide

/-- The book's first output line on `n = 2`: `|m| = 2` is a positive multiple of `n`, so `m` is one
block and `k₁` is added to it. (`List.modifyLast` does not reduce by `decide`, so the unkeyed part
is computed by `decide` and the last block by `List.modifyLast_concat`.) -/
example (k₁ k₂ : BitString 2) : cmacRpf 2 (k₁, k₂) [true, false] = [![true, false] + k₁] := by
  rw [cmacRpf, show cmacCore 2 [true, false] = (true, [] ++ [![true, false]]) by decide,
    List.modifyLast_concat]
  rfl

/-- The book's second output line on `n = 2`: `|m| = 3`, so `u = 1`, the blocks are `a₁ = 10` and
`a₂ = 1`, and the last block is `(a₂ ‖ 1 ‖ 0^(n-u-1)) ⊕ k₂ = 11 ⊕ k₂`. -/
example (k₁ k₂ : BitString 2) :
    cmacRpf 2 (k₁, k₂) [true, false, true] = [![true, false], ![true, true] + k₂] := by
  rw [cmacRpf, show cmacCore 2 [true, false, true] = (false, [![true, false]] ++ [![true, true]])
    by decide, List.modifyLast_concat]
  rfl

/-! ### Counterexamples for the added hypotheses -/

/-- On all lists, including `[]`, the one-key encoding is not `ε`-prefix-free for any `ε < 1`:
`[]` is a prefix of the encoding of `[0]` for every key. -/
example (X : Type*) [Fintype X] [Nonempty X] [AddGroup X] {ε : ℝ≥0∞} (hε : ε < 1) :
    ¬ IsRandPrefixFreeEncoding (PMF.uniformOfFintype X)
      (fun k (m : List X) => m.modifyLast (· + k)) ε := by
  intro h
  have hprob := h.prob_le (m₀ := []) (m₁ := [0]) (by simp)
  have hall : {k : X | PrefixCompatible (([] : List X).modifyLast (· + k))
      ([0].modifyLast (· + k))} = Set.univ :=
    Set.eq_univ_of_forall fun _ => Or.inl (List.nil_prefix)
  rw [hall, (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (by simp)] at hprob
  exact hprob.not_gt hε

/-- With `n = 0`, CMAC's encoding of `[]` is empty, so it is not randomized prefix-free. -/
example {ε : ℝ≥0∞} :
    ¬ IsRandPrefixFreeEncoding (PMF.uniformOfFintype (BitString 0 × BitString 0)) (cmacRpf 0) ε :=
  fun h => h.ne_nil (0, 0) [] (by decide)

/-- With `ℓ = 0`, the empty message has at most `n * 0` bits but one block. -/
example : ([] : List Bool).length ≤ 2 * 0 ∧ ¬ (cmacRpf 2 (0, 0) []).length ≤ 0 := by
  rw [cmacRpf, List.length_modifyLast]
  decide

/-- With one key `k₁ = k₂ = k`, the empty message and `1 ‖ 0^(n-1)` have the same encoding for
every `k` (`10` under XOR with `k` on 2-bit blocks). -/
theorem cmacRpf_nil_eq_single_key {n : ℕ} (hn : 0 < n) (k : BitString n) :
    cmacRpf n (k, k) [] = cmacRpf n (k, k) (true :: List.replicate (n - 1) false) := by
  have hpad : BitString.pad10star n [] = true :: List.replicate (n - 1) false :=
    BitString.pad10star_of_dvd hn (dvd_zero n)
  have hlen : (true :: List.replicate (n - 1) false).length = n := by simp; omega
  simp [cmacRpf, cmacCore, hpad, hlen, hn]

/-- Hence CMAC with a single key is not `ε`-prefix-free for any `ε < 1`. -/
example {n : ℕ} (hn : 0 < n) {ε : ℝ≥0∞} (hε : ε < 1) :
    ¬ IsRandPrefixFreeEncoding (PMF.uniformOfFintype (BitString n))
      (fun k m => cmacRpf n (k, k) m) ε := by
  intro h
  have hprob := h.prob_le (m₀ := []) (m₁ := true :: List.replicate (n - 1) false) (by simp)
  have hall : {k : BitString n | PrefixCompatible (cmacRpf n (k, k) [])
      (cmacRpf n (k, k) (true :: List.replicate (n - 1) false))} = Set.univ :=
    Set.eq_univ_of_forall fun k => Or.inl (by rw [cmacRpf_nil_eq_single_key hn])
  rw [hall, (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (by simp)] at hprob
  exact hprob.not_gt hε

end Cslib.Tests.RandPrefixFreeEncoding
