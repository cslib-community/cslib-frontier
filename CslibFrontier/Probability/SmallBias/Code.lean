/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.SmallBias
public import Mathlib.InformationTheory.Hamming

/-!
# Small-bias sample spaces and balanced linear codes

A sample space `G : σ → ι → Bool` (for a generator, `σ` is the set of seeds and `G s` the output
on the seed `s`) has a binary linear code `Cslib.BitString.sampleCode G`, which encodes a message
`v : ι → Bool` as the word `s ↦ v ⬝ᵥ G s` indexed by the seeds. Bit `s` of the codeword of the
`i`-th unit vector is bit `i` of `G s` (`Cslib.BitString.sampleCode_single`), and every
`Bool`-linear map `(ι → Bool) → (σ → Bool)` is the code of exactly one sample space
(`Cslib.BitString.sampleCode_injective`, `Cslib.BitString.sampleCode_ofCode`).

The distance between the codewords of `u ≠ v` is the number of seeds at which the parity on the
nonempty set `{i | u i ≠ v i}` is odd, and the bias of `G` on that set is one minus twice its
fraction. So `G`, with a uniform seed, is `ε`-biased exactly when the codewords of every two
distinct messages are at distance between `(1 - ε) |σ| / 2` and `(1 + ε) |σ| / 2`
(`Cslib.BitString.isSmallBias_map_iff_hammingDist_sampleCode`). With the seeds `σ = {0,1}^k` and
messages of `ℓ` bits, this is the correspondence of [Goldreich, Exercise 8.41][Goldreich2007DraftR4]
between `ε`-bias generators of stretch `ℓ` and binary linear codes from `ℓ`-bit strings to
`2^k`-bit strings whose codewords are pairwise at distance `(1 ± ε) 2^(k-1)`.

## Main definitions

* `Cslib.BitString.sampleCode`: the linear code of a sample space.

## Main results

* `Cslib.BitString.sampleCode_single`: the codeword of a unit vector lists one output bit per seed.
* `Cslib.BitString.sampleCode_ofCode`, `Cslib.BitString.sampleCode_injective`: sample spaces and
  binary linear codes correspond one to one.
* `Cslib.BitString.isSmallBias_map_iff_hammingDist_sampleCode`: small bias is the distance
  condition on the code.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft of March 2007,
  Exercise 8.41][Goldreich2007DraftR4]
-/

@[expose] public section

namespace Cslib.BitString

open Finset Probability

variable {σ ι : Type*} [Fintype ι]

/-- The binary linear code of a sample space `G`: the message `v` is encoded as the word whose
bit at the seed `s` is the parity `v ⬝ᵥ G s`. -/
def sampleCode (G : σ → ι → Bool) : (ι → Bool) →ₗ[Bool] σ → Bool where
  toFun v s := v ⬝ᵥ G s
  map_add' u v := funext fun s => add_dotProduct u v (G s)
  map_smul' c v := funext fun s => smul_dotProduct c v (G s)

@[simp]
theorem sampleCode_apply (G : σ → ι → Bool) (v : ι → Bool) (s : σ) :
    sampleCode G v s = v ⬝ᵥ G s :=
  rfl

/-- Bit `s` of the codeword of the `i`-th unit vector is bit `i` of the sample `G s`
[Goldreich, guideline to Exercise 8.41][Goldreich2007DraftR4]. -/
theorem sampleCode_single [DecidableEq ι] (G : σ → ι → Bool) (i : ι) (s : σ) :
    sampleCode G (Pi.single i true) s = G s i := by
  rw [sampleCode_apply, single_dotProduct]
  rfl

/-- Every binary linear code is the code of a sample space: the one whose sample at `s` lists the
bits at `s` of the codewords of the unit vectors. -/
theorem sampleCode_ofCode [DecidableEq ι] (C : (ι → Bool) →ₗ[Bool] σ → Bool) :
    sampleCode (fun s i => C (Pi.single i true) s) = C := by
  refine LinearMap.pi_ext fun i b => funext fun s => ?_
  cases b
  · simp [show (false : Bool) = 0 from rfl]
  · exact sampleCode_single _ i s

/-- Distinct sample spaces have distinct codes. -/
theorem sampleCode_injective :
    Function.Injective (sampleCode : (σ → ι → Bool) → (ι → Bool) →ₗ[Bool] σ → Bool) := by
  classical
  exact fun G H h => funext fun s => funext fun i => by
    simpa only [sampleCode_single] using congrFun (LinearMap.congr_fun h (Pi.single i true)) s

variable [Fintype σ]

/-- The codewords of `u` and `v` differ exactly at the seeds where the parity of `u + v` is odd. -/
theorem hammingDist_sampleCode (G : σ → ι → Bool) (u v : ι → Bool) :
    hammingDist (sampleCode G u) (sampleCode G v) = #{s | (u + v) ⬝ᵥ G s = true} := by
  rw [hammingDist]
  refine congrArg card (filter_congr fun s _ => ?_)
  simp only [sampleCode_apply, add_dotProduct]
  generalize u ⬝ᵥ G s = a
  generalize v ⬝ᵥ G s = b
  cases a <;> cases b <;> decide

/-- The bias of a sample space at the set where `w` is `true` is one minus twice the fraction of
the seeds at which the parity `w ⬝ᵥ G s` is odd. -/
private theorem bias_map_setOf [Nonempty σ] [DecidableEq ι] (G : σ → ι → Bool) (w : ι → Bool) :
    bias ((PMF.uniformOfFintype σ).map G) {i | w i} =
      1 - 2 * (#{s | w ⬝ᵥ G s = true} : ℝ) / Fintype.card σ := by
  have hc : (0 : ℝ) < Fintype.card σ := by exact_mod_cast Fintype.card_pos
  rw [bias_uniformOfFintype_map, Fintype.expect_eq_sum_div_card]
  simp_rw [← signVal_dotProduct]
  have h (s : σ) : signVal (w ⬝ᵥ G s) = 1 - 2 * (if w ⬝ᵥ G s = true then 1 else 0 : ℝ) := by
    cases w ⬝ᵥ G s <;> norm_num [signVal]
  rw [sum_congr rfl fun s _ => h s, sum_sub_distrib, ← mul_sum, sum_boole]
  field_simp
  simp

/-- A bias `1 - 2 N / c` lies in `[-ε, ε]` exactly when `N` lies between `(1 - ε) c / 2` and
`(1 + ε) c / 2`. -/
private theorem abs_one_sub_two_mul_div_le_iff {N c ε : ℝ} (hc : 0 < c) :
    |1 - 2 * N / c| ≤ ε ↔ (1 - ε) * c / 2 ≤ N ∧ N ≤ (1 + ε) * c / 2 := by
  rw [abs_le, mul_div_assoc, le_sub_iff_add_le, sub_le_comm]
  constructor
  · rintro ⟨h₁, h₂⟩
    have h₁' : 2 * N ≤ (1 + ε) * c := by
      have := mul_le_mul_of_nonneg_right (by linarith : 2 * (N / c) ≤ 1 + ε) hc.le
      rwa [mul_assoc, div_mul_cancel₀ _ hc.ne'] at this
    have h₂' : (1 - ε) * c ≤ 2 * N := by
      have := mul_le_mul_of_nonneg_right (by linarith : 1 - ε ≤ 2 * (N / c)) hc.le
      rwa [mul_assoc, div_mul_cancel₀ _ hc.ne'] at this
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    have hN : N / c * c = N := div_mul_cancel₀ _ hc.ne'
    constructor
    · nlinarith
    · nlinarith

/-- **Small-bias generators are balanced linear codes** [Goldreich, Exercise
8.41][Goldreich2007DraftR4]: a sample space `G`, with a uniform seed, is `ε`-biased exactly when
the codewords of any two distinct messages under its linear code `sampleCode G` are at Hamming
distance between `(1 - ε) |σ| / 2` and `(1 + ε) |σ| / 2`. For `σ = {0,1}^k` these bounds are
`(1 ± ε) 2^(k-1)`. -/
theorem isSmallBias_map_iff_hammingDist_sampleCode [Nonempty σ] [DecidableEq ι]
    (G : σ → ι → Bool) {ε : ℝ} :
    IsSmallBias ε ((PMF.uniformOfFintype σ).map G) ↔ ∀ u v : ι → Bool, u ≠ v →
      (1 - ε) * Fintype.card σ / 2 ≤ hammingDist (sampleCode G u) (sampleCode G v) ∧
        (hammingDist (sampleCode G u) (sampleCode G v) : ℝ) ≤ (1 + ε) * Fintype.card σ / 2 := by
  have hc : (0 : ℝ) < Fintype.card σ := by exact_mod_cast Fintype.card_pos
  constructor
  · intro hG u v huv
    have hw : ({i | (u + v) i} : Finset ι).Nonempty := by
      by_contra h
      refine huv (funext fun i => ?_)
      have hi : (u + v) i ≠ true := fun hi =>
        h ⟨i, by simpa using hi⟩
      revert hi
      simp only [Pi.add_apply]
      cases u i <;> cases v i <;> decide
    have := hG _ hw
    rw [bias_map_setOf, abs_one_sub_two_mul_div_le_iff hc] at this
    rwa [hammingDist_sampleCode]
  · intro h S hS
    have hS' : ({i | (fun i => decide (i ∈ S)) i} : Finset ι) = S := by
      ext; simp
    have hne : (fun i => decide (i ∈ S)) ≠ 0 := fun h0 => by
      obtain ⟨i, hi⟩ := hS
      simpa [hi] using congrFun h0 i
    have := h _ 0 hne
    rw [hammingDist_sampleCode, add_zero] at this
    rw [← hS', bias_map_setOf, abs_one_sub_two_mul_div_le_iff hc]
    exact this

end Cslib.BitString
