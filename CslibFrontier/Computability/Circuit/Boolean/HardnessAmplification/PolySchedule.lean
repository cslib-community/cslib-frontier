/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification
public import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.Schedule
public import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.WorstCase
public import CslibFrontier.Computability.Circuit.Boolean.Substitution
public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryField
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Polynomial worst-case hardness gives polynomial average-case hardness

The Sudan–Trevisan–Vadhan encoding `Cslib.Circuits.Boolean.hardnessEncode` turns a function `f` of
`n` bits that needs circuits of size polynomial in `n + s` into a function of `O (n + log s)` bits
that is average-case hard for size `s`
(`Cslib.HardnessEncoding.exists_isAverageCaseHard_polyEncode`). This is the polynomial regime of
the exponential schedule of `Cslib.HardnessEncoding.eventually_isAverageCaseHard_encodedSlice`.

**The schedule.** For a function `f` on `n` bits and a target size `s`, put
`l = ⌊log₂ (n + s + 1)⌋ + 1`.

* The block length is `b = 64 l + 2048` (`Cslib.HardnessEncoding.polyBlock`) and the field degree is
  `w = 4 b`: the explicit binary field `Cslib.BinaryField (4 * b)` with the additive equivalence
  `(Cslib.BinaryField.equivBits _).toEquiv` to `BitString (4 * b)` and the embedding
  `Cslib.BinaryField.embed` of `b`-bit blocks as polynomials of degree less than `b` (the same
  field and embedding as `Cslib.HardnessEncoding.encodedSlice`).
* The number of blocks is `m = n / b + 1` (`Cslib.HardnessEncoding.polyBlocks`), so `m b > n`. The
  function `f` is extended to `m b` bits by ignoring the last `m b - n` bits
  (`Cslib.HardnessEncoding.polyExtend`); its truth table is read with the blocks in the coordinate
  order of `Cslib.BitString.blocksEquiv`, block `i` consisting of the bits `i b, …, i b + b - 1`.
* The encoding has arity `m w + w = (m + 1) 4 b` (`Cslib.HardnessEncoding.polyArity`): the first
  `m w` bits are `m` field elements, each `w` bits wide, and the last `w` bits are the mask `r`
  (`Cslib.Circuits.Boolean.hardnessEncode`).
* The reconstruction has `σ = ⌊log₂ s⌋ + 1` (so `s < 2 ^ σ ≤ 2 s`), `K = 2 σ + ⌊log₂ w⌋ + 2` masks,
  Sudan parameter `D = 2 ^ (3 b - ⌊b / 4⌋)` and majority trees of depth `⌊log₂ (m b)⌋ + 1`, exactly
  as in `Cslib.HardnessEncoding.isAverageCaseHard_encodedSlice_of`.

**The argument.** A circuit of size `s` that agrees with the encoding on a `1 / 2 + 1 / s` fraction
yields a circuit for the extension of `f` with at most `2 ^ (40 b)` gates, and so one for `f` with
two more gates. Since `2 ^ l ≤ 2 (n + s + 1)`, `2 ^ (40 b) ≤ 2 ^ 84480 (n + s + 1) ^ 2560`.

## Main definitions

* `Cslib.HardnessEncoding.polyBlock`, `Cslib.HardnessEncoding.polyBlocks`,
  `Cslib.HardnessEncoding.polyArity`: the parameters of the schedule.
* `Cslib.HardnessEncoding.polyExtend`: the extension of `f` to whole blocks.
* `Cslib.HardnessEncoding.polyEncode`: the polynomial-regime encoding.

## Main results

* `Cslib.HardnessEncoding.polyArity_le`: the arity is linear in `n` plus logarithmic in `s`.
* `Cslib.HardnessEncoding.exists_isAverageCaseHard_polyEncode`: **polynomial worst-case hardness
  gives average-case hardness**.

## References

* [M. Sudan, L. Trevisan, S. Vadhan, *Pseudorandom generators without the XOR lemma*]
  [SudanTrevisanVadhan2001]
* [R. Impagliazzo, A. Wigderson, *P = BPP if E requires exponential circuits: Derandomizing the
  XOR lemma*][ImpagliazzoWigderson1997]
-/

@[expose] public section

namespace Cslib.HardnessEncoding

open Finset Cslib.Code Cslib.Circuits Cslib.Circuits.Boolean

/-! ### The schedule -/

/-- The block length `b = 64 (⌊log₂ (n + s + 1)⌋ + 1) + 2048`. -/
def polyBlock (n s : ℕ) : ℕ := 64 * (Nat.log 2 (n + s + 1) + 1) + 2048

/-- The number of blocks `m = n / b + 1`, so that `m b > n`. -/
def polyBlocks (n s : ℕ) : ℕ := n / polyBlock n s + 1

/-- The arity of the polynomial-regime encoding: `m w + w` for `w = 4 b`. -/
def polyArity (n s : ℕ) : ℕ :=
  polyBlocks n s * (4 * polyBlock n s) + 4 * polyBlock n s

/-- The block length is positive. -/
theorem polyBlock_pos (n s : ℕ) : 0 < polyBlock n s := by
  unfold polyBlock
  omega

/-- The blocks cover the `n` input bits. -/
theorem le_polyBlocks_mul (n s : ℕ) : n ≤ polyBlocks n s * polyBlock n s := by
  have := Nat.lt_div_mul_add (a := n) (b := polyBlock n s) (polyBlock_pos n s)
  unfold polyBlocks
  rw [add_mul, one_mul]
  omega

/-- The function `f` of `n` bits extended to `m b ≥ n` bits by ignoring the bits after the
first `n`. -/
def polyExtend (n s : ℕ) (f : BooleanFunction n) :
    BooleanFunction (polyBlocks n s * polyBlock n s) :=
  fun y => f fun i => y (Fin.castLE (le_polyBlocks_mul n s) i)

/-- **The polynomial-regime encoding** of a function `f` on `n` bits for hardness `s`: the
encoding `hardnessEncode` of the extension `polyExtend n s f` over the explicit binary field of
degree `4 b`, with `b = polyBlock n s`, its bit encoding `BinaryField.equivBits` and the
embedding `BinaryField.embed` of `b`-bit blocks. -/
noncomputable def polyEncode (n s : ℕ) (f : BooleanFunction n) : BooleanFunction (polyArity n s) :=
  hardnessEncode (BinaryField.equivBits (w := 4 * polyBlock n s)
    (by have := polyBlock_pos n s; omega)).toEquiv
    (BinaryField.embed (by have := polyBlock_pos n s; omega) (by omega)) (polyExtend n s f)

/-- **The arity is linear in `n` plus logarithmic in `s`**: `polyArity n s ≤ c (n + ⌊log₂ (n + s +
1)⌋ + 1)`. -/
theorem polyArity_le : ∃ c : ℕ, ∀ n s : ℕ, polyArity n s ≤ c * (n + Nat.log 2 (n + s + 1) + 1) := by
  refine ⟨20000, fun n s => ?_⟩
  have h1 := le_polyBlocks_mul n s
  have h2 : polyBlocks n s * polyBlock n s ≤ n + polyBlock n s := by
    unfold polyBlocks
    rw [add_mul, one_mul]
    have := Nat.div_mul_le_self n (polyBlock n s)
    omega
  have h3 : polyArity n s = 4 * (polyBlocks n s * polyBlock n s) + 4 * polyBlock n s := by
    unfold polyArity
    ring
  have h4 : polyBlock n s = 64 * (Nat.log 2 (n + s + 1) + 1) + 2048 := rfl
  omega

/-! ### Hardness at one length -/

/-- `B < 2 ^ ⌊B / 48⌋` for `B ≥ 480`. -/
private theorem lt_two_pow_div {B : ℕ} (hB : 480 ≤ B) : B < 2 ^ (B / 48) := by
  have key : ∀ k, 10 ≤ k → 48 * (k + 1) ≤ 2 ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      have : 48 ≤ 2 ^ k :=
        calc 48 ≤ 2 ^ 10 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      rw [pow_succ]
      omega
  have := key (B / 48) (by omega)
  omega

/-! ### Polynomial hardness -/

/-- **Polynomial worst-case hardness gives average-case hardness**
[SudanTrevisanVadhan2001], [ImpagliazzoWigderson1997]. If a function `f` of `n` bits needs more
than `c (n + s + 1) ^ c` gates, then its polynomial-regime encoding on `polyArity n s` bits (linear
in `n` plus logarithmic in `s`, `Cslib.HardnessEncoding.polyArity_le`) is average-case hard for
size `s ≥ 2`. -/
theorem exists_isAverageCaseHard_polyEncode : ∃ c : ℕ, ∀ (n s : ℕ) (f : BooleanFunction n),
    2 ≤ s → c * (n + s + 1) ^ c < complexity interpretation (single f) →
      IsAverageCaseHard (polyEncode n s f) s := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = 2560 + 81920 := ⟨_, rfl⟩
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℕ, c0 = 2 ^ N := ⟨_, rfl⟩
  have hc0lt : 4096 ≤ c0 := by
    rw [hc0]
    calc 4096 = 2 ^ 12 := by norm_num
      _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨2 * c0, fun n s f hs hhard => ?_⟩
  generalize hPdef : 2 * c0 * (n + s + 1) ^ (2 * c0) = P at hhard
  obtain ⟨x, hx⟩ : ∃ x, x = n + s + 1 := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l, l = Nat.log 2 x + 1 := ⟨_, rfl⟩
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = Nat.log 2 s + 1 := ⟨_, rfl⟩
  set B := polyBlock n s with hBdef
  set M := polyBlocks n s with hMdef
  have hB : B = 64 * l + 2048 := by rw [hBdef, hl, hx]; rfl
  have hM : M = n / B + 1 := by rw [hMdef, hBdef]; rfl
  have hxpos : 0 < x := by omega
  have hxl : x < 2 ^ l := by rw [hl]; exact Nat.lt_pow_succ_log_self (by norm_num) x
  have h2l : 2 ^ l ≤ 2 * x := by
    have := Nat.pow_log_le_self 2 hxpos.ne'
    rw [hl, pow_succ]
    omega
  have hMl : M ≤ 2 ^ l := by
    have := Nat.div_le_self n B
    omega
  have hσl : σ ≤ l := by
    have : Nat.log 2 s ≤ Nat.log 2 x := Nat.log_mono_right (by omega)
    omega
  have hsσ : s < 2 ^ σ := by rw [hσdef]; exact Nat.lt_pow_succ_log_self (by norm_num) s
  -- the numeric hypotheses
  have hB6 : B ^ 6 ≤ 2 ^ (B / 8) := by
    calc B ^ 6 ≤ (2 ^ (B / 48)) ^ 6 := Nat.pow_le_pow_left (lt_two_pow_div (by omega)).le 6
      _ = 2 ^ (B / 48 * 6) := (pow_mul 2 (B / 48) 6).symm
      _ ≤ 2 ^ (B / 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hM1 : 1 ≤ M := by rw [hM]; exact Nat.le_add_left 1 _
  have hev : (2 ^ 27 * M ^ 3 + 4608 * M + 128) * B ^ 6 ≤ 2 ^ (B / 4) := by
    have hM3 : M ≤ M ^ 3 := Nat.le_self_pow (by norm_num) M
    calc (2 ^ 27 * M ^ 3 + 4608 * M + 128) * B ^ 6 ≤ (2 ^ 28 * M ^ 3) * B ^ 6 := by
          gcongr
          omega
      _ ≤ (2 ^ 28 * (2 ^ l) ^ 3) * 2 ^ (B / 8) := by gcongr
      _ = 2 ^ (28 + l * 3 + B / 8) := by rw [← pow_mul, ← pow_add, ← pow_add]
      _ ≤ 2 ^ (B / 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- the hardness of the extension
  have hbig : 2 ^ (40 * B) ≤ c0 * x ^ 2560 :=
    calc 2 ^ (40 * B) = (2 ^ l) ^ 2560 * 2 ^ 81920 := by
          rw [hB, ← pow_mul, ← pow_add]
          exact congrArg _ (by ring)
      _ ≤ (2 * x) ^ 2560 * 2 ^ 81920 := by gcongr
      _ = c0 * x ^ 2560 := by
          rw [hc0, hN, mul_pow, mul_right_comm, ← pow_add]
  have hxc : x ^ 2560 ≤ x ^ (2 * c0) := pow_le_pow_right₀ (by omega : 1 ≤ x) (by omega)
  have hbig2 : ∀ X : ℕ, x ^ 2560 ≤ X → 2 ^ (40 * B) + 2 ^ (40 * B) ≤ 2 * c0 * X := by
    intro X hX
    calc 2 ^ (40 * B) + 2 ^ (40 * B) = 2 * 2 ^ (40 * B) := (two_mul _).symm
      _ ≤ 2 * (c0 * x ^ 2560) := Nat.mul_le_mul_left 2 hbig
      _ ≤ 2 * (c0 * X) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hX)
      _ = 2 * c0 * X := (mul_assoc _ _ _).symm
  have hA2 : 2 ≤ 2 ^ (40 * B) :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (40 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hext : complexity interpretation (single f) ≤
      complexity interpretation (single (polyExtend n s f)) + 2 :=
    complexity_le_extend (le_polyBlocks_mul n s) f
  have hP := hbig2 _ hxc
  rw [hx, hPdef] at hP
  have hhard' : 2 ^ (40 * B) ≤ complexity interpretation (single (polyExtend n s f)) := by
    generalize 2 ^ (40 * B) = A at hA2 hP ⊢
    omega
  have key := card_agree_hardnessEncode_div_le (M := M) (B := B) (σ := σ) hM1
    (by omega) hev (by omega) (polyExtend n s f) hhard'
  refine IsAverageCaseHard.mono (s := 2 ^ σ) ?_ (by omega) hsσ.le
  exact fun g hg => key g (hg.trans (by omega))

end Cslib.HardnessEncoding
