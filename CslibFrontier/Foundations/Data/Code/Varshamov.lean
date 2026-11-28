/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.BallVolume
public import CslibFrontier.Foundations.Data.Code.ParityCheck
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Lindsey
import CslibFrontier.Tactic.LinarithCast
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Binary linear codes at rate `1 - H(δ)`

**Varshamov's bound** for binary linear codes: if fewer than `2 ^ c` nonzero words of `𝔽₂^ι` are
to be avoided, some matrix with `c` rows maps all of them to nonzero vectors
(`Cslib.Code.exists_mulVec_ne_zero_of_card_lt`), since a fixed nonzero word lies in the kernel of
exactly half of the rows. Applied to the nonzero words of weight less than `δ m`, whose number
the entropy bound controls, this gives a linear code `𝔽₂ⁿ → 𝔽₂ᵐ` of relative distance `δ`
whenever `n ≤ m (1 - H(δ))` and `δ ≤ 1 / 2`
(`Cslib.Code.exists_linearMap_injective_and_le_hammingDist`). Here `H(δ)` is the binary entropy
in bits, `Real.binEntropy δ / Real.log 2`.

Rounding the length gives three statements of Arora and Barak [AroraBarak09], each for every `n`
rather than for large `n`, and each with a linear code:

* Lemma 17.9, at length `⌊2n / (1 - H(δ))⌋` (`Cslib.Code.exists_linearMap_two_mul`);
* Exercise 17.6, the Gilbert–Varshamov bound at length `⌈n / (1 - H(δ))⌉`
  (`Cslib.Code.exists_linearMap_ceil_div`);
* Exercise 17.10(b), linear codes at length `⌈1.1 n / (1 - H(δ))⌉`
  (`Cslib.Code.exists_linearMap_ceil_mul_div`).

## Main results

* `Cslib.Code.exists_mulVec_ne_zero_of_card_lt`: Varshamov's union bound.
* `Cslib.Code.exists_linearMap_injective_and_le_hammingDist`: linear codes of relative distance
  `δ` at rate `1 - H(δ)`.
* `Cslib.Code.exists_linearMap_two_mul`, `Cslib.Code.exists_linearMap_ceil_div`,
  `Cslib.Code.exists_linearMap_ceil_mul_div`: Arora–Barak Lemma 17.9 and Exercises 17.6 and
  17.10(b).

## References

* [R. R. Varshamov, *Estimate of the number of signals in error correcting codes*][Varshamov1957]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], draft of
  2007-01-08, Lemma 17.9 and Chapter 17, Exercises 6 and 10(b)
-/

public section

namespace Cslib.Code

open Finset Matrix Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A nonzero word of `𝔽₂^ι` is orthogonal to exactly half of the words: the signs
`(-1) ^ (r ⬝ᵥ x)` cancel (`Matrix.sum_neg_one_pow_val_dotProduct`). -/
private theorem card_filter_dotProduct_eq_zero_mul_two {x : ι → ZMod 2} (hx : x ≠ 0) :
    #{r : ι → ZMod 2 | r ⬝ᵥ x = 0} * 2 = 2 ^ Fintype.card ι := by
  have hsign (z : ZMod 2) : (-1 : ℝ) ^ z.val = if z = 0 then 1 else -1 := by
    obtain rfl | rfl : z = 0 ∨ z = 1 := by revert z; decide
    · simp
    · simp [ZMod.val_one]
  have h := sum_neg_one_pow_val_dotProduct x
  simp only [hx, ite_false, hsign, sum_ite, sum_const, nsmul_eq_mul, mul_one, mul_neg] at h
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (ι → ZMod 2)))
    fun r => r ⬝ᵥ x = 0
  rw [card_univ, Fintype.card_fun, ZMod.card] at hsplit
  have hR : (#{r : ι → ZMod 2 | r ⬝ᵥ x = 0} : ℝ) * 2 = 2 ^ Fintype.card ι := by
    have := congrArg (Nat.cast (R := ℝ)) hsplit
    cast_linarith
  exact_mod_cast hR

omit [DecidableEq ι] in
/-- **Varshamov's union bound** [Varshamov1957]. If a set `B` of nonzero words of `𝔽₂^ι` has fewer
than `2 ^ c` elements, some matrix with `c` rows maps every element of `B` to a nonzero vector:
a fixed nonzero word lies in the kernel of a `2 ^ (-c)` fraction of the matrices. -/
theorem exists_mulVec_ne_zero_of_card_lt {B : Finset (ι → ZMod 2)} (h0 : 0 ∉ B) {c : ℕ}
    (hB : #B < 2 ^ c) : ∃ H : Matrix (Fin c) ι (ZMod 2), ∀ x ∈ B, H *ᵥ x ≠ 0 := by
  classical
  by_contra! hbad
  have hcover : (univ : Finset (Matrix (Fin c) ι (ZMod 2))) ⊆
      B.biUnion fun x => {H : Matrix (Fin c) ι (ZMod 2) | ∀ y ∈ ({x} : Finset _), H *ᵥ y = 0} := by
    intro H _
    obtain ⟨x, hx, hHx⟩ := hbad H
    exact mem_biUnion.2 ⟨x, hx, by simpa using hHx⟩
  have hle := (card_le_card hcover).trans card_biUnion_le
  have hcard : Fintype.card (Matrix (Fin c) ι (ZMod 2)) = 2 ^ (Fintype.card ι * c) := by
    change Fintype.card (Fin c → ι → ZMod 2) = _
    simp [ZMod.card, ← pow_mul, mul_comm]
  rw [sum_congr rfl fun x _ => card_filter_forall_mulVec_eq_zero {x} c, card_univ, hcard] at hle
  have hsum : (∑ x ∈ B, #{r : ι → ZMod 2 | ∀ y ∈ ({x} : Finset _), r ⬝ᵥ y = 0} ^ c) * 2 ^ c =
      #B * 2 ^ (Fintype.card ι * c) := by
    rw [sum_mul, sum_congr rfl fun x hx => ?_, sum_const, smul_eq_mul]
    have h := card_filter_dotProduct_eq_zero_mul_two (ι := ι) (x := x) (fun hx0 => h0 (hx0 ▸ hx))
    simp only [mem_singleton, forall_eq]
    rw [← mul_pow, h, pow_mul]
  have := Nat.mul_le_mul_right (2 ^ c) hle
  rw [hsum, mul_comm #B] at this
  have := Nat.le_of_mul_le_mul_left this (by positivity)
  omega

/-- **Linear codes at rate `1 - H(δ)`.** For `0 ≤ δ ≤ 1 / 2` and `n ≤ m (1 - H(δ))`, where
`H(δ) = Real.binEntropy δ / Real.log 2` is the binary entropy in bits, there is an injective linear
map `E : 𝔽₂ⁿ → 𝔽₂ᵐ` whose distinct codewords differ in at least `δ m` positions. -/
theorem exists_linearMap_injective_and_le_hammingDist {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    {n m : ℕ} (h : (n : ℝ) ≤ m * (1 - binEntropy δ / log 2)) :
    ∃ E : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2), Function.Injective E ∧
      ∀ x y, x ≠ y → δ * m ≤ hammingDist (E x) (E y) := by
  have hlog : 0 < log 2 := log_pos one_lt_two
  have hH₀ : 0 ≤ binEntropy δ := binEntropy_nonneg hδ₀ (by linarith)
  have hnm : n ≤ m := by
    exact_mod_cast h.trans (mul_le_of_le_one_right (Nat.cast_nonneg m)
      (sub_le_self _ (div_nonneg hH₀ hlog.le)))
  -- The nonzero words of weight less than `δ m`.
  set B : Finset (Fin m → ZMod 2) := {x | x ≠ 0 ∧ (hammingNorm x : ℝ) < δ * m}
  have hB : #B < 2 ^ (m - n) := by
    have hcard := card_le_card (s := insert 0 B) (t := {y | hammingDist 0 y ≤ ⌊δ * m⌋₊})
      fun x hx => by
        simp only [mem_filter, mem_univ, true_and, hammingDist_zero_left]
        rcases mem_insert.1 hx with rfl | hx
        · simp
        · exact Nat.le_floor (mem_filter.1 hx).2.2.le
    rw [card_insert_of_notMem (by simp [B])] at hcard
    have hvol := card_filter_hammingDist_le_le_exp_mul_qaryEntropy (β := fun _ : Fin m => ZMod 2)
      (q := 2) (fun _ => ZMod.card 2) 0 (α := δ) (by norm_num; linarith)
      (by rw [Fintype.card_fin]; exact Nat.floor_le (by positivity))
    rw [Fintype.card_fin, qaryEntropy_two] at hvol
    have hexp : exp (m * binEntropy δ) ≤ 2 ^ (m - n) := by
      rw [← rpow_natCast, Nat.cast_sub hnm, ← exp_log two_pos, ← exp_mul, exp_le_exp]
      have h' := mul_le_mul_of_nonneg_right h hlog.le
      have e : (m : ℝ) * (1 - binEntropy δ / log 2) * log 2 = m * log 2 - m * binEntropy δ := by
        field_simp
      linarith
    have : (#B : ℝ) < 2 ^ (m - n) := by cast_linarith [hcard]
    exact_mod_cast this
  obtain ⟨H, hH⟩ := exists_mulVec_ne_zero_of_card_lt (by simp [B]) hB
  -- The kernel of `H` has dimension at least `n`.
  have hdim : n ≤ Module.finrank (ZMod 2) (parityCheckCode H) := by
    have := card_le_finrank_parityCheckCode_add H
    simp only [Fintype.card_fin] at this
    omega
  obtain ⟨f, hf⟩ := Module.Free.exists_linearMap_injective_of_linearIndependent_of_rank_le
    (M := Fin n → ZMod 2) (Module.finBasis (ZMod 2) (parityCheckCode H)).linearIndependent
    (by rw [rank_fin_fun, Cardinal.mk_fin]; exact_mod_cast hdim)
  refine ⟨(parityCheckCode H).subtype ∘ₗ f, Subtype.val_injective.comp hf, fun x y hxy => ?_⟩
  by_contra! hlt
  set z := ((parityCheckCode H).subtype ∘ₗ f) (y - x)
  have hz : z ≠ 0 := fun h0 => hxy.symm (sub_eq_zero.1 (Subtype.val_injective.comp hf (by
    simpa [z] using h0)))
  rw [_root_.hammingDist_eq_hammingNorm, neg_add_eq_sub, ← map_sub] at hlt
  exact hH z (mem_filter.2 ⟨mem_univ _, hz, hlt⟩) (mem_parityCheckCode.1 (f (y - x)).property)

/-- `1 - H(δ)` is positive for `0 ≤ δ < 1 / 2`. -/
private theorem sub_binEntropy_div_log_two_pos {δ : ℝ} (hδ : δ < 1 / 2) :
    0 < 1 - binEntropy δ / log 2 := by
  rw [sub_pos, div_lt_one (log_pos one_lt_two), binEntropy_lt_log_two]
  norm_num at hδ ⊢
  linarith

/-- **Constant-rate codes exist** [Arora and Barak, Lemma 17.9][AroraBarak09]. For `0 ≤ δ < 1 / 2`
and every `n`, there is an injective map `E : {0,1}ⁿ → {0,1}ᵐ`, here linear, with
`m = ⌊2n / (1 - H(δ))⌋` and relative distance `δ`: distinct codewords differ in at least `δ m`
positions. `H(δ) = Real.binEntropy δ / Real.log 2` is the binary entropy in bits. The draft states
this for large `n` and leaves the length unrounded. -/
theorem exists_linearMap_two_mul {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ : δ < 1 / 2) (n : ℕ) :
    ∃ E : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin ⌊2 * n / (1 - binEntropy δ / log 2)⌋₊ → ZMod 2),
      Function.Injective E ∧ ∀ x y, x ≠ y →
        δ * ⌊2 * n / (1 - binEntropy δ / log 2)⌋₊ ≤ hammingDist (E x) (E y) := by
  have ha := sub_binEntropy_div_log_two_pos hδ
  refine exists_linearMap_injective_and_le_hammingDist hδ₀ hδ.le ?_
  set a := 1 - binEntropy δ / log 2
  have ha1 : a ≤ 1 := sub_le_self _ (div_nonneg (binEntropy_nonneg hδ₀ (by linarith))
    (log_pos one_lt_two).le)
  have hfl := Nat.lt_floor_add_one (2 * n / a)
  rw [div_lt_iff₀ ha] at hfl
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero]; positivity
  · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith

/-- **The Gilbert–Varshamov bound** [Arora and Barak, Exercise 17.6][AroraBarak09]. For
`0 ≤ δ < 1 / 2` and every `n`, there is an injective map `E : {0,1}ⁿ → {0,1}ᵐ`, here linear, with
`m = ⌈n / (1 - H(δ))⌉` and relative distance `δ`. `H(δ) = Real.binEntropy δ / Real.log 2` is the
binary entropy in bits. The draft states this for large `n` and leaves the length unrounded. -/
theorem exists_linearMap_ceil_div {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ : δ < 1 / 2) (n : ℕ) :
    ∃ E : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin ⌈n / (1 - binEntropy δ / log 2)⌉₊ → ZMod 2),
      Function.Injective E ∧ ∀ x y, x ≠ y →
        δ * ⌈n / (1 - binEntropy δ / log 2)⌉₊ ≤ hammingDist (E x) (E y) :=
  exists_linearMap_injective_and_le_hammingDist hδ₀ hδ.le
    ((div_le_iff₀ (sub_binEntropy_div_log_two_pos hδ)).1 (Nat.le_ceil _))

/-- **Linear codes** [Arora and Barak, Exercise 17.10(b)][AroraBarak09], corrected. For
`0 ≤ δ < 1 / 2` and every `n`, there is an injective linear map `E : {0,1}ⁿ → {0,1}ᵐ` with
`m = ⌈1.1 n / (1 - H(δ))⌉` and relative distance `δ`. `H(δ) = Real.binEntropy δ / Real.log 2` is
the binary entropy in bits. The draft says "for every `δ > 0`", which fails for `δ ≥ 1 / 2`:
the length is undefined at `δ = 1 / 2`, and Plotkin's bound (Exercise 17.7) rules out `2 ^ n`
codewords of relative distance above `1 / 2` for large `n`. -/
theorem exists_linearMap_ceil_mul_div {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ : δ < 1 / 2) (n : ℕ) :
    ∃ E : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin ⌈1.1 * n / (1 - binEntropy δ / log 2)⌉₊ → ZMod 2),
      Function.Injective E ∧ ∀ x y, x ≠ y →
        δ * ⌈1.1 * n / (1 - binEntropy δ / log 2)⌉₊ ≤ hammingDist (E x) (E y) := by
  have ha := sub_binEntropy_div_log_two_pos hδ
  refine exists_linearMap_injective_and_le_hammingDist hδ₀ hδ.le ?_
  have := (div_le_iff₀ ha).1 (Nat.le_ceil (1.1 * n / (1 - binEntropy δ / log 2)))
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

end Cslib.Code
