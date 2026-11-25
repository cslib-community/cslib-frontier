/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BPP.Derandomization.Generator
public import CslibFrontier.Computability.Complexity.FineGrained.FunctionRates
public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.GreedyDesignSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation

/-!
# An exponential-time set system for the Nisan–Wigderson generator

Goldreich [Exercise 8.19][Goldreich2007DraftR4] asks, for every `γ > 0`, for a set system as in
Condition 2 of Theorem 8.18 with `m(k) = Ω(k)` and `ℓ(k) = 2 ^ Ω(k)`: an exponential-time
computable function `S` such that, for every `k` and `i, j ∈ [ℓ(k)]`, the set `S(k, i)` is a
subset of `[k]` with `m(k)` elements and `|S(k, i) ∩ S(k, j)| ≤ γ m(k)` for `i ≠ j`.

The construction is the guideline's: the `i`-th set of the greedy design
`Cslib.Crypto.PRG.NisanWigderson.greedyMasks` on `[k]` (scan the subsets of `[k]` of the block
size, keep one when it meets every kept one in few elements). For an integer `q ≥ 2` and
`t = ⌊k / (10 q² + 1)⌋`, the design `Cslib.Crypto.PRG.NisanWigderson.expDesign q` has blocks of
`m(k) = q t` elements, two of them sharing at most `t ≤ m(k) / q` elements, and at least
`2 ^ (t + 1)` blocks by the counting bound
`Cslib.Crypto.PRG.NisanWigderson.two_pow_succ_le_length_greedyMasks`, in place of the guideline's
probabilistic argument. Taking `q ≥ 1 / γ` gives the exercise
(`Cslib.Crypto.PRG.NisanWigderson.exists_computableInExpTime_design`).

A subset of `[k]` is given by its characteristic word of length `k`, read as a `Finset (Fin k)` by
`Cslib.Crypto.PRG.NisanWigderson.maskBlock`. The input `(k, i)` has `k` in unary and `i` in binary,
and exponential time is `Cslib.Complexity.ComputableInExpTime` in the parameter `k`: time
`O(2 ^ (δ k) (L + 1) ^ e)` on inputs of length `L`. The greedy scan is polynomial in `2 ^ k`
(`Cslib.Crypto.PRG.NisanWigderson.computableInPolyTime_greedyMasks`), so it runs in polynomial
time on the input padded by `2 ^ k` in unary, and writing the padding costs `2 ^ O(k)`
(`Turing.MultiTapeTM.ComputableInPolyTime.exists_computableInO_pad`).

## Main definitions

* `Cslib.Crypto.PRG.NisanWigderson.expDesign`: the greedy set system with parameter `q`.

## Main results

* `Cslib.Crypto.PRG.NisanWigderson.computableInExpTime_expDesign`: it is exponential-time
  computable.
* `Cslib.Crypto.PRG.NisanWigderson.length_expDesign`,
  `Cslib.Crypto.PRG.NisanWigderson.card_maskBlock_expDesign`,
  `Cslib.Crypto.PRG.NisanWigderson.card_maskBlock_inter_expDesign_le`: for `k ≥ 10 q² + 1` and
  indices below `2 ^ (t + 1)`, sets of `[k]` with `q t` elements meeting in at most `t`.
* `Cslib.Crypto.PRG.NisanWigderson.exists_computableInExpTime_design`: Goldreich Exercise 8.19.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*][Goldreich2007DraftR4],
  Exercise 8.19 and Theorem 8.18
-/

public section

namespace Cslib.Crypto.PRG.NisanWigderson

open Finset Turing.MultiTapeTM

/-- The greedy set system with parameter `q`, for `t = ⌊k / (10 q² + 1)⌋`: the `i`-th mask of
the greedy design on `[k]` with blocks of `q t` elements sharing at most `t` of them, or the empty
word when the design has at most `i` masks. -/
def expDesign (q k i : ℕ) : List Bool :=
  (greedyMasks k (q * (k / (10 * q ^ 2 + 1))) (k / (10 * q ^ 2 + 1))).getD i []

variable {q k i : ℕ}

/-- For `k ≥ 10 q² + 1` and `q ≥ 2`, the greedy design behind `expDesign q k` has at least
`2 ^ (t + 1)` masks, for `t = ⌊k / (10 q² + 1)⌋`. -/
private theorem two_pow_le_length (hq : 2 ≤ q) (hk : 10 * q ^ 2 + 1 ≤ k) :
    2 ^ (k / (10 * q ^ 2 + 1) + 1) ≤
      (greedyMasks k (q * (k / (10 * q ^ 2 + 1))) (k / (10 * q ^ 2 + 1))).length := by
  set B := 10 * q ^ 2 + 1
  set t := k / B
  have ht : 0 < t := Nat.div_pos hk (by omega)
  refine two_pow_succ_le_length_greedyMasks (by nlinarith) ?_
  calc 10 * (q * t) ^ 2 < t * B * t := by
        simp only [B]
        nlinarith
    _ ≤ k * t := Nat.mul_le_mul_right t (Nat.div_mul_le_self k B)

private theorem mem_of_lt (hq : 2 ≤ q) (hk : 10 * q ^ 2 + 1 ≤ k)
    (hi : i < 2 ^ (k / (10 * q ^ 2 + 1) + 1)) :
    expDesign q k i = (greedyMasks k (q * (k / (10 * q ^ 2 + 1))) (k / (10 * q ^ 2 + 1)))[i]'
      (hi.trans_le (two_pow_le_length hq hk)) := by
  rw [expDesign, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some]

/-- Every set of `expDesign q k` below `2 ^ (t + 1)` is a mask on `[k]`. -/
theorem length_expDesign (hq : 2 ≤ q) (hk : 10 * q ^ 2 + 1 ≤ k)
    (hi : i < 2 ^ (k / (10 * q ^ 2 + 1) + 1)) : (expDesign q k i).length = k := by
  rw [mem_of_lt hq hk hi]
  exact length_of_mem_greedyMasks (List.getElem_mem _)

/-- The block of `Design.greedy` at an index below `2 ^ (t + 1)` is the set of `expDesign`. -/
private theorem block_greedy (hq : 2 ≤ q) (hk : 10 * q ^ 2 + 1 ≤ k)
    (hi : i < 2 ^ (k / (10 * q ^ 2 + 1) + 1)) :
    (Design.greedy k (q * (k / (10 * q ^ 2 + 1))) (k / (10 * q ^ 2 + 1))
      (2 ^ (k / (10 * q ^ 2 + 1) + 1)) (two_pow_le_length hq hk)).block ⟨i, hi⟩ =
      maskBlock k (expDesign q k i) := by
  rw [mem_of_lt hq hk hi]
  rfl

/-- Every set of `expDesign q k` below `2 ^ (t + 1)` has `q t` elements. -/
theorem card_maskBlock_expDesign (hq : 2 ≤ q) (hk : 10 * q ^ 2 + 1 ≤ k)
    (hi : i < 2 ^ (k / (10 * q ^ 2 + 1) + 1)) :
    #(maskBlock k (expDesign q k i)) = q * (k / (10 * q ^ 2 + 1)) := by
  rw [← block_greedy hq hk hi]
  exact Design.card_block _ _

/-- Two distinct sets of `expDesign q k` below `2 ^ (t + 1)` share at most `t` elements. -/
theorem card_maskBlock_inter_expDesign_le (hq : 2 ≤ q) (hk : 10 * q ^ 2 + 1 ≤ k) {j : ℕ}
    (hi : i < 2 ^ (k / (10 * q ^ 2 + 1) + 1)) (hj : j < 2 ^ (k / (10 * q ^ 2 + 1) + 1))
    (hij : i ≠ j) :
    #(maskBlock k (expDesign q k i) ∩ maskBlock k (expDesign q k j)) ≤ k / (10 * q ^ 2 + 1) := by
  rw [← block_greedy hq hk hi, ← block_greedy hq hk hj]
  exact Design.card_inter_le _ (Fin.ne_of_val_ne hij)

/-! ### Exponential time -/

/-- `expDesign q` on inputs padded by a unary `N`: the seed length is cut to `⌊log₂ N⌋`, so that
the greedy scan is polynomial in the padded input. -/
private def paddedDesign (q : ℕ) (x : (ℕ × ℕ) × ℕ) : List Bool :=
  let s := min x.1.1 (Nat.log 2 x.2)
  (greedyMasks s (q * (s / (10 * q ^ 2 + 1))) (s / (10 * q ^ 2 + 1))).getD x.1.2 []

private theorem paddedDesign_two_pow (q k i : ℕ) :
    paddedDesign q ((k, i), 2 ^ k) = expDesign q k i := by
  simp only [paddedDesign, Nat.log_pow (by norm_num : 1 < 2), min_self, expDesign]

private theorem computableInPolyTime_paddedDesign (q : ℕ) :
    ComputableInPolyTime (paddedDesign q) (encPair (encPair encUnary encNat) encUnary) encBits := by
  set enc := encPair (encPair encUnary encNat) encUnary
  have hs : ComputableInPolyTime (fun x : (ℕ × ℕ) × ℕ => min x.1.1 (Nat.log 2 x.2)) enc
      encUnary :=
    .unary_min' ((ComputableInPolyTime.fst encUnary encNat).comp (.fst _ _))
      (ComputableInPolyTime.binary_log_two.comp
        (ComputableInPolyTime.unary_to_binary.comp (.snd _ _)))
  have ht := (ComputableInPolyTime.unary_div_const (10 * q ^ 2 + 1)).comp hs
  exact ComputableInPolyTime.listGetD_binary (encA := encBits) []
    (computableInPolyTime_greedyMasks hs (.unary_mul' (.const q) ht) ht (by growth_poly))
    ((ComputableInPolyTime.snd encUnary encNat).comp (.fst _ _))

/-- **The greedy set system is exponential-time computable.** On inputs `(k, i)` with `k` in
unary and `i` in binary, `expDesign q` is computable within time `O(2 ^ (δ k) (L + 1) ^ e)`, for
some `δ`. -/
theorem computableInExpTime_expDesign (q : ℕ) :
    ∃ δ : ℝ, Complexity.ComputableInExpTime (fun p : ℕ × ℕ => expDesign q p.1 p.2)
      (encPair encUnary encNat) encBits (fun p => p.1) δ := by
  obtain ⟨C, D, h⟩ := (computableInPolyTime_paddedDesign q).exists_computableInO_pad
    (ν := fun p : ℕ × ℕ => p.1) (.fst _ _)
  have heq : (fun p : ℕ × ℕ => expDesign q p.1 p.2) = fun p => paddedDesign q (p, 2 ^ p.1) :=
    funext fun p => (paddedDesign_two_pow q p.1 p.2).symm
  rw [heq]
  refine ⟨D, Complexity.ComputableInExpTime.of_computableInO h C D fun p => ?_⟩
  rw [show (D : ℝ) * (p.1 : ℝ) = ((D * p.1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  push_cast
  ring_nf
  rfl

/-- **Goldreich Exercise 8.19** [Goldreich2007DraftR4]: for every `γ > 0` there is an
exponential-time computable set system `S` as in Condition 2 of Theorem 8.18, with
`m(k) = Ω(k)` and `ℓ(k) = 2 ^ Ω(k)`. The set `S(k, i)` is the subset `maskBlock k (S (k, i))` of
`[k]` given by its characteristic word of length `k`. For every `k` and `i, j < ℓ(k)`, it has
`m(k)` elements, and two distinct ones share at most `γ m(k)` elements; `m(k) ≥ c k` and
`ℓ(k) ≥ 2 ^ (c k)` for a constant `c > 0` and all `k ≥ k₀`. Exponential time is
`Cslib.Complexity.ComputableInExpTime` in the parameter `k`, on inputs `(k, i)` with `k` in unary
and `i` in binary. -/
theorem exists_computableInExpTime_design {γ : ℝ} (hγ : 0 < γ) :
    ∃ (S : ℕ × ℕ → List Bool) (ℓ m : ℕ → ℕ) (δ c : ℝ) (k₀ : ℕ),
      Complexity.ComputableInExpTime S (encPair encUnary encNat) encBits (fun p => p.1) δ ∧
      (∀ k i, i < ℓ k → (S (k, i)).length = k ∧ #(maskBlock k (S (k, i))) = m k) ∧
      (∀ k i j, i < ℓ k → j < ℓ k → i ≠ j →
        (#(maskBlock k (S (k, i)) ∩ maskBlock k (S (k, j))) : ℝ) ≤ γ * m k) ∧
      0 < c ∧ ∀ k ≥ k₀, c * k ≤ m k ∧ (2 : ℝ) ^ (c * k) ≤ ℓ k := by
  set q := max 2 ⌈γ⁻¹⌉₊
  set B := 10 * q ^ 2 + 1
  have hq : 2 ≤ q := le_max_left _ _
  have hγq : 1 ≤ γ * q :=
    calc (1 : ℝ) = γ * γ⁻¹ := (mul_inv_cancel₀ hγ.ne').symm
      _ ≤ γ * q := mul_le_mul_of_nonneg_left
        ((Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)) hγ.le
  have hB : (0 : ℝ) < B := by positivity
  obtain ⟨δ, hδ⟩ := computableInExpTime_expDesign q
  refine ⟨fun p => expDesign q p.1 p.2, fun k => if B ≤ k then 2 ^ (k / B + 1) else 0,
    fun k => q * (k / B), δ, 1 / (2 * B), 2 * B, hδ, fun k i hi => ?_, fun k i j hi hj hij => ?_,
    by positivity, fun k hk => ?_⟩
  · have hk : B ≤ k := by by_contra h; simp [h] at hi
    simp only [hk, ite_true] at hi
    exact ⟨length_expDesign hq hk hi, card_maskBlock_expDesign hq hk hi⟩
  · have hk : B ≤ k := by by_contra h; simp [h] at hi
    simp only [hk, ite_true] at hi hj
    calc (#(maskBlock k (expDesign q k i) ∩ maskBlock k (expDesign q k j)) : ℝ)
        ≤ (k / B : ℕ) := mod_cast card_maskBlock_inter_expDesign_le hq hk hi hj hij
      _ ≤ γ * q * (k / B : ℕ) := le_mul_of_one_le_left (Nat.cast_nonneg _) hγq
      _ = γ * ((q * (k / B) : ℕ) : ℝ) := by
        push_cast
        ring
  · have hkB : B ≤ k := by omega
    simp only [hkB, ite_true]
    -- `⌊k / B⌋ ≥ k / (2 B)` once `k ≥ 2 B`
    have hhalf : 1 / (2 * B) * (k : ℝ) ≤ (k / B : ℕ) := by
      rw [one_div, mul_inv_rev, mul_assoc, inv_mul_le_iff₀ hB]
      have : (k : ℝ) < (k / B : ℕ) * B + B := mod_cast Nat.lt_div_mul_add (by omega : 0 < B)
      have : (2 * B : ℝ) ≤ k := mod_cast hk
      linarith
    refine ⟨hhalf.trans ?_, ?_⟩
    · push_cast
      exact le_mul_of_one_le_left (Nat.cast_nonneg _) (by exact_mod_cast (by omega : 1 ≤ q))
    · push_cast
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)

end Cslib.Crypto.PRG.NisanWigderson
