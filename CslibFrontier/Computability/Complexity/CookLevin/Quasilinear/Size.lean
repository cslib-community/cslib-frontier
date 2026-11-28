/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Clause

/-!
# The size of the clause indices and variables of the quasilinear formula

The clause indices and the variables of the quasilinear formula are written with
`Layout.addressBits` and `Layout.variableBits` bits. Every quantity of the layout is `2 ^ n`
times a polynomial in `n` (the number of records is `2 ^ (n + κ + 1)`, the other parameters are
polynomial in `n`), so both numbers of bits are `n + O (log n)`.

## Main results

* `Cslib.Complexity.CookLevin.Quasilinear.Layout.exists_addressBits_le`: the clause indices
  take `n + 5 log (n + 2) + c` bits.
* `Cslib.Complexity.CookLevin.Quasilinear.Layout.exists_variableBits_le`: the variables take
  `n + 5 log (n + 2) + c` bits.
-/

public section

namespace Cslib.Complexity.CookLevin.Quasilinear

open Cslib.BitonicSort

/-- The number of layers of the sorting network on `2 ^ τ` positions is at most `(τ + 1) ^ 2`. -/
private theorem schedule_length_le (τ : ℕ) : (schedule τ).length ≤ (τ + 1) ^ 2 := by
  induction τ with
  | zero => simp [schedule]
  | succ τ ih =>
    rw [schedule_succ, List.length_append]
    have h : (mergeLayers (τ + 1) (τ + 1)).length = τ + 1 := by simp [mergeLayers]
    rw [h]
    linarith

/-- A number below `2 ^ n * (D * (n + 2) ^ d)` takes `n + d log (n + 2) + D + d` bits. -/
private theorem clog_le_of_le_mul (D d n x : ℕ) (h : x ≤ 2 ^ n * (D * (n + 2) ^ d)) :
    Nat.clog 2 x ≤ n + d * Nat.log 2 (n + 2) + (D + d) := by
  have h1 : D < 2 ^ D := Nat.lt_two_pow_self
  have h2 : n + 2 < 2 ^ (Nat.log 2 (n + 2) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h3 : (n + 2) ^ d ≤ (2 ^ (Nat.log 2 (n + 2) + 1)) ^ d := Nat.pow_le_pow_left h2.le d
  have h4 : x ≤ 2 ^ (n + d * Nat.log 2 (n + 2) + (D + d)) := by
    calc x ≤ 2 ^ n * (D * (n + 2) ^ d) := h
      _ ≤ 2 ^ n * (2 ^ D * (2 ^ (Nat.log 2 (n + 2) + 1)) ^ d) :=
        Nat.mul_le_mul le_rfl (Nat.mul_le_mul h1.le h3)
      _ = 2 ^ (n + D + (Nat.log 2 (n + 2) + 1) * d) := by
        rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num)
        (by linarith)
  exact Nat.clog_le_of_le_pow h4

namespace Layout

/-- Both counted quantities are below `2 ^ n` times a constant times `(n + 2) ^ 5`. -/
private theorem exists_bounds (k S κ R : ℕ) : ∃ D : ℕ, ∀ n : ℕ,
    36 * (Layout.mk k S n κ).MAXI * (Layout.mk k S n κ).G R ≤ 2 ^ n * (D * (n + 2) ^ 5) ∧
    (Layout.mk k S n κ).AUX + 9 * (Layout.mk k S n κ).MAXI * (Layout.mk k S n κ).A R + 1 ≤
      2 ^ n * (D * (n + 2) ^ 5) := by
  obtain ⟨B, hB⟩ : ∃ B, B = S + 8 * k + 2 * κ + 10 := ⟨_, rfl⟩
  refine ⟨2 ^ (κ + 1) * B ^ 5 * (216 * (k + 2) * (2 * k + 5 * R + 58) + 24 * (k + 2) +
    54 * (k + 2) * (2 * k + 5 * R + 50) + 1), fun n => ?_⟩
  set Λ : Layout := Layout.mk k S n κ with hΛ
  have hτ : Λ.τ = n + κ + 1 := rfl
  have hW : Λ.W = n + κ + 3 := rfl
  have hI : Λ.I = n + 2 := rfl
  have hC : Λ.C = S + 8 + 8 * k := rfl
  have hP : Λ.P = Λ.τ + Λ.W + 4 := rfl
  have hN : Λ.N = 2 ^ n * 2 ^ (κ + 1) := by
    change 2 ^ (n + κ + 1) = 2 ^ n * 2 ^ (κ + 1)
    rw [← pow_add, Nat.add_assoc]
  have hN1 : 0 < Λ.N := by
    rw [hN]; exact Nat.mul_pos (Nat.pow_pos (by norm_num)) (Nat.pow_pos (by norm_num))
  have hL : Λ.L ≤ (Λ.τ + 1) ^ 2 := schedule_length_le Λ.τ
  obtain ⟨q, hq⟩ : ∃ q, q = B * (n + 2) := ⟨_, rfl⟩
  have hBn : 2 * n ≤ B * n := Nat.mul_le_mul_right n (by omega)
  have hqe : q = B * n + 2 * B := by rw [hq]; ring
  have hτq : Λ.τ + 1 ≤ q := by omega
  have hWq : Λ.W ≤ q := by omega
  have hIq : Λ.I ≤ q := by omega
  have hCq : Λ.C ≤ q := by omega
  have hPq : Λ.P + 1 ≤ q := by omega
  have hSq : S ≤ q := by omega
  have hq1 : 0 < q := by omega
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have hq3 : q ≤ q ^ 3 := by
    simpa using Nat.pow_le_pow_right hq1 (show 1 ≤ 3 by norm_num)
  have hq35 : q ^ 3 ≤ q ^ 5 := Nat.pow_le_pow_right hq1 (by norm_num)
  have hLq : Λ.L ≤ q ^ 2 := hL.trans (Nat.pow_le_pow_left hτq 2)
  have hRB : Λ.RB ≤ (k + 2) * q := by
    have h := Nat.mul_le_mul_left k hWq
    change Λ.C + Λ.I + k * Λ.W ≤ _
    linarith
  have hkL : k * Λ.L + 1 ≤ (k + 2) * q ^ 2 := by
    have h := Nat.mul_le_mul_left k hLq
    linarith
  have hinner : Λ.inner ≤ Λ.N * (2 * (k + 2) * q ^ 3) := by
    have h1 : Λ.inner ≤ Λ.N * ((k + 2) * q) + ((k + 2) * q ^ 2) * Λ.N * q := by
      change Λ.N * Λ.RB + (k * Λ.L + 1) * Λ.N * (Λ.P + 1) ≤ _
      exact Nat.add_le_add (Nat.mul_le_mul_left _ hRB)
        (Nat.mul_le_mul (Nat.mul_le_mul_right _ hkL) hPq)
    linarith [Nat.mul_le_mul_left (Λ.N * (k + 2)) hq3]
  have hpos : 0 < Λ.N * ((k + 2) * q ^ 3) :=
    Nat.mul_pos hN1 (Nat.mul_pos (by omega) (Nat.pow_pos hq1))
  have hAUX : Λ.AUX ≤ Λ.N * (24 * (k + 2) * q ^ 3) := by
    change 8 * Λ.inner + 8 ≤ _
    linarith
  have hLp1 : Λ.L + 1 ≤ 2 * q ^ 2 := by omega
  have hMAXI : Λ.MAXI ≤ 6 * Λ.N * (k + 2) * q ^ 4 := by
    calc Λ.MAXI ≤ 3 * Λ.N * q * (k + 2) * (2 * q ^ 2) * q := by
          change 3 * Λ.N * Λ.I * (k + 1) * (Λ.L + 1) * (Λ.P + 1) ≤ _
          exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl hIq)
            (by omega)) hLp1) hPq
      _ = 6 * Λ.N * (k + 2) * q ^ 4 := by ring
  have hA : Λ.A R ≤ (2 * k + 5 * R + 50) * q := by
    have h1 := Nat.mul_le_mul_left k hWq
    have h2 := Nat.mul_le_mul_right R hCq
    have h3 : R ≤ R * q := Nat.le_mul_of_pos_right R hq1
    change 2 * (S + Λ.I + k * Λ.W + 2) + 4 * Λ.C * R + R + 4 * Λ.I + 4 + 9 * Λ.W +
      5 * (Λ.τ + Λ.W) + 2 * Λ.W + 4 ≤ _
    linarith
  have hG : Λ.G R ≤ (2 * k + 5 * R + 58) * q := by
    change Λ.A R + 8 ≤ _
    linarith
  have hpos5 : 0 < Λ.N * q ^ 5 := Nat.mul_pos hN1 (Nat.pow_pos hq1)
  have hfin : Λ.N * q ^ 5 = 2 ^ n * (2 ^ (κ + 1) * B ^ 5 * (n + 2) ^ 5) := by
    rw [hN, hq]; ring
  constructor
  · calc 36 * Λ.MAXI * Λ.G R ≤ 36 * (6 * Λ.N * (k + 2) * q ^ 4) *
          ((2 * k + 5 * R + 58) * q) := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hMAXI) hG
      _ = Λ.N * q ^ 5 * (216 * (k + 2) * (2 * k + 5 * R + 58)) := by ring
      _ ≤ Λ.N * q ^ 5 * (216 * (k + 2) * (2 * k + 5 * R + 58) + 24 * (k + 2) +
          54 * (k + 2) * (2 * k + 5 * R + 50) + 1) := Nat.mul_le_mul le_rfl (by omega)
      _ = _ := by rw [hfin]; ring
  · have e1 : Λ.N * (24 * (k + 2) * q ^ 3) ≤ Λ.N * q ^ 5 * (24 * (k + 2)) := by
      linarith [Nat.mul_le_mul_left (Λ.N * (24 * (k + 2))) hq35]
    have e2 : 9 * Λ.MAXI * Λ.A R ≤ Λ.N * q ^ 5 * (54 * (k + 2) * (2 * k + 5 * R + 50)) := by
      calc 9 * Λ.MAXI * Λ.A R ≤ 9 * (6 * Λ.N * (k + 2) * q ^ 4) *
            ((2 * k + 5 * R + 50) * q) := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hMAXI) hA
        _ = _ := by ring
    calc Λ.AUX + 9 * Λ.MAXI * Λ.A R + 1 ≤ Λ.N * q ^ 5 * (24 * (k + 2)) +
          Λ.N * q ^ 5 * (54 * (k + 2) * (2 * k + 5 * R + 50)) + Λ.N * q ^ 5 * 1 := by
          linarith [hAUX.trans e1]
      _ = Λ.N * q ^ 5 * (24 * (k + 2) + 54 * (k + 2) * (2 * k + 5 * R + 50) + 1) := by ring
      _ ≤ Λ.N * q ^ 5 * (216 * (k + 2) * (2 * k + 5 * R + 58) + 24 * (k + 2) +
          54 * (k + 2) * (2 * k + 5 * R + 50) + 1) := Nat.mul_le_mul le_rfl (by omega)
      _ = _ := by rw [hfin]; ring

/-- The clause indices of the formula take `n + 5 log (n + 2) + c` bits, with `c` depending on the
machine only. -/
theorem exists_addressBits_le (k S κ R : ℕ) : ∃ c : ℕ, ∀ n : ℕ,
    (Layout.mk k S n κ).addressBits R ≤ n + 5 * Nat.log 2 (n + 2) + c := by
  obtain ⟨D, hD⟩ := exists_bounds k S κ R
  exact ⟨D + 5, fun n => clog_le_of_le_mul D 5 n _ (hD n).1⟩

/-- The variables of the formula take `n + 5 log (n + 2) + c` bits, with `c` depending on the
machine only. -/
theorem exists_variableBits_le (k S κ R : ℕ) : ∃ c : ℕ, ∀ n : ℕ,
    (Layout.mk k S n κ).variableBits R ≤ n + 5 * Nat.log 2 (n + 2) + c := by
  obtain ⟨D, hD⟩ := exists_bounds k S κ R
  exact ⟨D + 5, fun n => clog_le_of_le_mul D 5 n _ (hD n).2⟩

/-- Every clause index fits in `addressBits` bits. -/
theorem le_two_pow_addressBits (Λ : Layout) (R : ℕ) :
    36 * Λ.MAXI * Λ.G R ≤ 2 ^ Λ.addressBits R :=
  Nat.le_pow_clog (by norm_num) _

/-- Every variable fits in `variableBits` bits. -/
theorem lt_two_pow_variableBits (Λ : Layout) (R : ℕ) :
    Λ.AUX + 9 * Λ.MAXI * Λ.A R < 2 ^ Λ.variableBits R :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_pow_clog (by norm_num) _)

end Layout

end Cslib.Complexity.CookLevin.Quasilinear
