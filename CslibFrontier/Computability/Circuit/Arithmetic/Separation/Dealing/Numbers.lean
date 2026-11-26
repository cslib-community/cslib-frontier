/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.ProgramTime

/-!
# The numbers of one cut

The cut of the dealing program of [AnthropicVPVNP2026] (`isCut_dealProgram_of_evaluatesGroups`)
has explicit numbers: the time of its pieces, their size and its own time. For the numbers of
one cut of Theorem J.3 (`CutNumbers`: a bound `m` of the polylogarithmic factors, the scale `v`,
the time `τ` and the size `s` of the instance, the number `k` by which it is cut, the `K` blocks
of `T` steps, and bounds for the numbers of the plan), these are at most `τ * m ^ 10 / k`
(`CutNumbers.time_le`), `(s / k + τ / v ^ 256) * m ^ 10` (`CutNumbers.size_le`) and
`(s + τ * k / v ^ 256) * m ^ 10` (`CutNumbers.dealTime_le`).

## Main definitions

* `CutNumbers`: the numbers of one cut.

## Main results

* `CutNumbers.time_le`: the time of the pieces.
* `CutNumbers.size_le`: the size of the pieces.
* `CutNumbers.dealTime_le`: the time of the dealing program.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: Theorem J.3 (p. 53: a
program cuts `(τ, s)` into `(τΛ/k, (s/k + τ/v^256)Λ)` in `(s + τk/v^256)Λ` steps), with
`m = Λ`. Ported from the source module `Nc.Dl.Num0`, on the constants of P1's `groupTime_le`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Dealing

/-- The numbers of one cut: `m` bounds the polylogarithmic factors and the constants, `v` is the
scale, `τ` and `s` are the time and the size of the instance, which is cut by `k`, into `K`
blocks of `T` steps with parts of `ℓ` letters; units have `ub` bits, base parties at most `lh`
units at the beginning, and `X` bounds the numbers that depend on `K` only. A group has at most
`ιb` base parties, `bd` units with one holder in it and `ev` cells and units read by its roles,
and there are `mm` groups. The codes have `Lc` bits and the letters `c`. -/
structure CutNumbers (v K τ s k T ℓ ub lh X Lc m c ιb bd ev mm : ℕ) : Prop where
  /-- The bound of the polylogarithmic factors is large. -/
  le_m : 10000 ≤ m
  /-- It is at most the scale. -/
  m_le_v : m ≤ v
  /-- The instance is cut. -/
  k_pos : 0 < k
  /-- Into at most `K` blocks. -/
  k_le_K : k ≤ K
  /-- The blocks take at most `τ * m` steps. -/
  KT_le : K * T ≤ τ * m
  /-- The parts have `s / K + 1` letters. -/
  ℓ_eq : ℓ = s / K + 1
  /-- Units have bits. -/
  ub_pos : 0 < ub
  /-- At most `T + 1`. -/
  ub_le : ub ≤ T + 1
  /-- The units at the beginning of a base party have at most `m * T` bits. -/
  lh_mul_ub_le : lh * ub ≤ m * T
  /-- The codes have fewer than `m` bits. -/
  Lc_lt : Lc < m
  /-- The codes of the letters are short. -/
  c_le : 4 * c + 2 ≤ m
  /-- `X` bounds the number of blocks. -/
  K_le_X : K ≤ X
  /-- A group has at most `m * K / k` base parties. -/
  ιb_mul_le : ιb * k ≤ m * K
  /-- And at most `X`. -/
  ιb_le_X : ιb ≤ X
  /-- The units with one holder in a group have few bits. -/
  bd_le : bd * ub * v ^ 300 ≤ τ * m ^ 2
  /-- The cells and the units read by the roles of a group have few bits. -/
  ev_le : ev * ub * k ≤ τ * m ^ 2
  /-- There are at most `k * m` groups. -/
  mm_le : mm ≤ k * m
  /-- And at most `X`. -/
  mm_le_X : mm ≤ X
  /-- What depends on `K` only is small. -/
  small : X ^ 6 * m ^ 20 * v ^ 300 ≤ τ

namespace CutNumbers

variable {v K τ s k T ℓ ub lh X Lc m c ιb bd ev mm : ℕ}
  (h : CutNumbers v K τ s k T ℓ ub lh X Lc m c ιb bd ev mm)
include h

private theorem one_le_m : 1 ≤ m := le_trans (by norm_num) h.le_m

private theorem pos_v : 0 < v := lt_of_lt_of_le (by have := h.le_m; omega) h.m_le_v

private theorem one_le_X : 1 ≤ X := h.k_pos.trans_le (h.k_le_K.trans h.K_le_X)

/-- What depends on `K` only is at most `τ / v ^ 256`. -/
private theorem small_le : X ^ 6 * m ^ 20 ≤ τ / v ^ 256 := by
  rw [Nat.le_div_iff_mul_le (Nat.pow_pos h.pos_v)]
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right h.pos_v (by norm_num))).trans h.small

/-- The units with one holder in a group have at most `τ / v ^ 256` bits. -/
private theorem bd_mul_ub_le : bd * ub ≤ τ / v ^ 256 := by
  rw [Nat.le_div_iff_mul_le (Nat.pow_pos h.pos_v)]
  refine Nat.le_of_mul_le_mul_right (?_ : _ ≤ τ * v ^ 44) (Nat.pow_pos h.pos_v)
  calc bd * ub * v ^ 256 * v ^ 44 = bd * ub * v ^ 300 := by ring
    _ ≤ τ * m ^ 2 := h.bd_le
    _ ≤ τ * v ^ 44 := Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left h.m_le_v 2).trans
        (Nat.pow_le_pow_right h.pos_v (by norm_num)))

/-- Monomials in `X` and `m` increase with their degrees. -/
private theorem pow_mul_pow_le {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    X ^ a * m ^ b ≤ X ^ a' * m ^ b' :=
  Nat.mul_le_mul (Nat.pow_le_pow_right h.one_le_X ha) (Nat.pow_le_pow_right h.one_le_m hb)

/-- **The time of the pieces.** For `κ ≤ m`, `κ` times the time of GROUP at a script is at most
`τ * m ^ 10 / k`. -/
theorem time_le {κ : ℕ} (hκ : κ ≤ m) :
    κ * ((Lc + 1) * (T + ub + 2) + ιb * T + 3 * (ev + ιb * lh) * (ub + Lc + 1) + 10 * X ^ 3) ≤
      τ * m ^ 10 / k := by
  rw [Nat.le_div_iff_mul_le h.k_pos]
  have hm := h.one_le_m
  have hX := h.one_le_X
  have hm4 : 28 * m ^ 5 ≤ m ^ 10 := by
    nlinarith [Nat.pow_le_pow_left h.le_m 5, Nat.one_le_pow 5 m hm]
  -- `k` and the blocks
  have hkτ : X ^ 4 ≤ τ := by
    simpa using (h.pow_mul_pow_le (a := 4) (b := 0) (a' := 6) (b' := 20) (by norm_num)
      (by norm_num)).trans (h.small_le.trans (Nat.div_le_self _ _))
  have hk : k ≤ X := h.k_le_K.trans h.K_le_X
  have hTk : T * k ≤ τ * m := (Nat.mul_le_mul_left T h.k_le_K).trans (by linarith [h.KT_le])
  -- the terms
  have t₁ : (Lc + 1) * (T + ub + 2) * k ≤ m * (2 * T + 3) * k :=
    Nat.mul_le_mul_right k (Nat.mul_le_mul h.Lc_lt (by have := h.ub_le; omega))
  have t₂ := Nat.mul_le_mul_right T h.ιb_mul_le
  have t₃ : 3 * (ev + ιb * lh) * (ub + Lc + 1) * k ≤ 3 * (ev + ιb * lh) * (2 * (ub * m)) * k :=
    Nat.mul_le_mul_right k (Nat.mul_le_mul_left _ (by nlinarith [h.Lc_lt, h.ub_pos]))
  have t₄ := Nat.mul_le_mul_left (6 * m) (Nat.mul_le_mul h.ιb_mul_le h.lh_mul_ub_le)
  have t₅ := Nat.mul_le_mul_left (10 * X ^ 3) hk
  have hkτ' : k ≤ τ := hk.trans ((Nat.le_self_pow (by norm_num) X).trans hkτ)
  have q (j : ℕ) (hj : j ≤ 4) : τ * m ^ j ≤ τ * m ^ 4 :=
    Nat.mul_le_mul_left τ (Nat.pow_le_pow_right hm hj)
  have hB : ((Lc + 1) * (T + ub + 2) + ιb * T + 3 * (ev + ιb * lh) * (ub + Lc + 1) + 10 * X ^ 3) *
      k ≤ 28 * τ * m ^ 4 := by
    have ⟨_, _, _, _⟩ : _ ∧ _ ∧ _ ∧ _ :=
      ⟨q 0 (by decide), q 1 (by decide), q 2 (by decide), q 3 (by decide)⟩
    simp only [pow_zero, pow_one, mul_one] at *
    linarith [pow_succ X 3, Nat.mul_le_mul_left m hTk, Nat.mul_le_mul_left m hkτ',
      Nat.mul_le_mul_left m h.KT_le, Nat.mul_le_mul_left (6 * m) h.ev_le,
      Nat.mul_le_mul_left (6 * m ^ 3) h.KT_le]
  calc κ * (_ : ℕ) * k ≤ m * (28 * τ * m ^ 4) := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul hκ hB
    _ = τ * (28 * m ^ 5) := by ring
    _ ≤ τ * m ^ 10 := Nat.mul_le_mul_left _ hm4

/-- **The size of the pieces** is at most `(s / k + τ / v ^ 256) * m ^ 10`. -/
theorem size_le : X + 1 + (200 * X ^ 3 * Lc + ιb * ℓ * (4 * c + 2) + bd * (4 * ub)) ≤
    (s / k + τ / v ^ 256) * m ^ 10 := by
  have hm := h.one_le_m
  -- the letters of the parts of a group
  have hι : ιb * ℓ ≤ m * (s / k) + m + X := by
    have : ιb * (s / K) ≤ m * (s / k) + m := by
      refine Nat.le_of_mul_le_mul_right (?_ : _ ≤ (m * (s / k) + m) * k) h.k_pos
      calc ιb * (s / K) * k = ιb * k * (s / K) := by ring
        _ ≤ m * K * (s / K) := Nat.mul_le_mul_right _ h.ιb_mul_le
        _ = m * (K * (s / K)) := by ring
        _ ≤ m * (k * (s / k + 1)) := Nat.mul_le_mul_left _
            ((Nat.mul_div_le s K).trans (Nat.lt_mul_div_succ s h.k_pos).le)
        _ = (m * (s / k) + m) * k := by ring
    rw [h.ℓ_eq, Nat.mul_add, Nat.mul_one]; linarith [h.ιb_le_X]
  generalize s / k = S at hι
  generalize hW : τ / v ^ 256 = W
  have h₁ := Nat.mul_le_mul hι h.c_le
  have h₂ : bd * ub ≤ W := hW ▸ h.bd_mul_ub_le
  have h₃ : X + 1 + 200 * X ^ 3 * Lc + (m * m + X * m) ≤ W := by
    refine le_trans ?_ (hW ▸ h.small_le)
    have := h.pow_mul_pow_le (a := 3) (b := 3) (a' := 6) (b' := 20) (by decide) (by decide)
    have := Nat.mul_le_mul_left (X ^ 3 * m ^ 2) h.le_m
    have := Nat.mul_le_mul_left (200 * X ^ 3) h.Lc_lt.le
    let pm (a b : ℕ) (ha : a ≤ 3 := by decide) (hb : b ≤ 2 := by decide) := h.pow_mul_pow_le ha hb
    have ⟨_, _, _, _, _⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ := ⟨pm 0 0, pm 1 0, pm 0 2, pm 1 1, pm 3 1⟩
    simp only [pow_zero, pow_one, one_mul, mul_one] at *
    linarith
  have := Nat.mul_le_mul_left S (Nat.pow_le_pow_right hm (by decide : 2 ≤ 10))
  have := Nat.mul_le_mul_left W (((by decide : 5 ≤ 10000).trans h.le_m).trans
    (Nat.le_self_pow (by decide : 10 ≠ 0) m))
  linarith

/-- **The time of the dealing program** is at most `(s + τ * k / v ^ 256) * m ^ 10`, with at most
`mm * bd` cut units. -/
theorem dealTime_le : dealTime Lc X K mm ub (mm * bd) s ≤ (s + τ * k / v ^ 256) * m ^ 10 := by
  have hm := h.one_le_m
  have hX := h.one_le_X
  have hL := h.Lc_lt
  have hkW : k * (τ / v ^ 256) ≤ τ * k / v ^ 256 := by
    rw [Nat.mul_comm τ k]; exact Nat.mul_div_le_mul_div_assoc k τ _
  -- the cut units
  have hcut : mm * bd * ((ub + 1) * (60 * Lc + 100)) ≤ 200 * m ^ 2 * (τ * k / v ^ 256) := by
    calc mm * bd * ((ub + 1) * (60 * Lc + 100)) ≤ k * m * bd * ((2 * ub) * (100 * m)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right bd h.mm_le)
            (Nat.mul_le_mul (by have := h.ub_pos; omega)
              (by omega))
      _ = 200 * m ^ 2 * (k * (bd * ub)) := by ring
      _ ≤ 200 * m ^ 2 * (τ * k / v ^ 256) := by grw [h.bd_mul_ub_le, hkW]
  -- what depends on `K` only
  have hY : 1 ≤ X * m := Nat.mul_le_mul hX hm
  have hR : K * (60 * Lc + 100) + K * (60 * Lc + 130) +
      (4 * (X * X) + 7 * X) * (stepBound Lc X + 30) + X * (90 * Lc + 230) +
        mm * (pieceBound Lc X + 60) + 300 ≤ τ * k / v ^ 256 := by
    have hXY : X ≤ X * m := Nat.le_mul_of_pos_right X hm
    have hLY : Lc ≤ X * m := hL.le.trans (Nat.le_mul_of_pos_left m hX)
    calc _ ≤ X * m * (60 * (X * m) + 100) + X * m * (60 * (X * m) + 130) +
          (4 * (X * m * (X * m)) + 7 * (X * m)) * (stepBound (X * m) (X * m) + 30) +
          X * m * (90 * (X * m) + 230) + X * m * (pieceBound (X * m) (X * m) + 60) + 300 := by
          have := h.K_le_X
          have := h.mm_le_X
          unfold stepBound pieceBound
          gcongr <;> omega
      _ ≤ 30000 * (X * m) ^ 5 := by
          generalize X * m = Y at hY
          unfold stepBound pieceBound
          let py {k} (hk : k ≤ 5 := by decide) := Nat.pow_le_pow_right hY hk
          have ⟨_, _, _, _⟩ : _ ∧ _ ∧ _ ∧ _ := ⟨py (k := 1), py (k := 2), py (k := 3), py (k := 4)⟩
          simp only [pow_one] at *
          linarith
      _ ≤ m * m * (X * m) ^ 5 :=
          Nat.mul_le_mul_right _ (le_trans (by norm_num) (Nat.mul_le_mul h.le_m h.le_m))
      _ = X ^ 5 * m ^ 7 := by ring
      _ ≤ X ^ 6 * m ^ 20 := h.pow_mul_pow_le (by norm_num) (by norm_num)
      _ ≤ τ / v ^ 256 := h.small_le
      _ ≤ τ * k / v ^ 256 := (Nat.le_mul_of_pos_left _ h.k_pos).trans hkW
  -- the word of the argument
  have hs : 60 * s + s * (60 * Lc + 100) ≤ s * m ^ 10 := by
    have h210 : m ^ 2 ≤ m ^ 10 := Nat.pow_le_pow_right hm (by norm_num)
    have : 60 * Lc + 160 ≤ m ^ 10 := le_trans (by nlinarith [h.le_m]) h210
    nlinarith
  have := Nat.mul_le_mul_left (τ * k / v ^ 256) (by
    have h310 : m ^ 3 ≤ m ^ 10 := Nat.pow_le_pow_right hm (by norm_num)
    linarith [Nat.mul_le_mul_left (m ^ 2) h.le_m, Nat.one_le_pow 2 m hm] : 200 * m ^ 2 + 1 ≤ m ^ 10)
  unfold dealTime
  linarith

end CutNumbers

end Cslib.Circuits.Arithmetic.Separation.Dealing
