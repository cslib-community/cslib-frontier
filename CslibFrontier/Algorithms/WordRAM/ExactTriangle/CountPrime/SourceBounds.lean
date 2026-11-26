/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CountPrime.Flat
import CslibFrontier.Foundations.Data.Nat.ClogPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Original-input logarithmic width and polynomial wider prefixes

When the original modulus and weights are polynomially bounded in n+2, the concrete counter
admits logarithmic physical width and every wider execution has polynomial words and memory
support, independently of that chosen width. The modulus bound is explicit; these are not
uniform bounds for arbitrarily large runtime p relative to n.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM

private theorem envelope_le_pow {n p A κ : ℕ}
    (hp : p ≤ (n + 2) ^ κ) (hA : A ≤ (n + 2) ^ κ) :
    envelope n p A ≤ (n + 2) ^ (κ + 21) := by
  let b := n + 2
  let k := Nat.clog 2 n
  let e := κ + 12
  change p ≤ b ^ κ at hp
  change A ≤ b ^ κ at hA
  have hb : 2 ≤ b := by dsimp only [b]; omega
  have hκ : 1 ≤ b ^ κ := Nat.one_le_pow _ _ (by omega)
  have hle (j : ℕ) (hj : j ≤ κ + 12) : b ^ j ≤ b ^ e := Nat.pow_le_pow_right (by omega) hj
  have htwo : 2 ^ k ≤ b ^ 2 :=
    (Nat.pow_le_pow_right (by decide) (Nat.clog_mono_right 2 (Nat.le_add_right n 2))).trans
      (Nat.two_pow_clog_le_sq (by omega))
  have hfour : 4 ^ k ≤ b ^ 4 := by
    calc
      _ = (2 ^ k) ^ 2 := by simp only [pow_two, ← mul_pow]; norm_num
      _ ≤ (b ^ 2) ^ 2 := Nat.pow_le_pow_left htwo _
      _ = b ^ 4 := by rw [← pow_mul]
  have hsixteen : 16 ^ k ≤ b ^ 8 := by
    change (2 ^ 4) ^ k ≤ b ^ 8
    rw [← pow_mul, Nat.mul_comm 4 k, pow_mul]
    exact (Nat.pow_le_pow_left htwo 4).trans_eq (by rw [← pow_mul])
  have hN2 : n * n ≤ b ^ e :=
    (pow_two n).symm.trans_le
      ((Nat.pow_le_pow_left (Nat.le_add_right n 2) 2).trans (hle 2 (by omega)))
  have hN3 : n * n * n ≤ b ^ e :=
    (pow_three' n).symm.trans_le
      ((Nat.pow_le_pow_left (Nat.le_add_right n 2) 3).trans (hle 3 (by omega)))
  have hnE : n ≤ b ^ e :=
    (Nat.le_add_right n 2).trans ((pow_one b).symm.trans_le (hle 1 (by omega)))
  have hkE : k ≤ b ^ e := (Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le).trans hnE
  have hpE : p ≤ b ^ e := hp.trans (hle _ (by omega))
  have hAE : A ≤ b ^ e := hA.trans (hle _ (by omega))
  have hfourE : 4 ^ k ≤ b ^ e := hfour.trans (hle _ (by omega))
  have htwoE : 2 ^ k ≤ b ^ e := htwo.trans (hle _ (by omega))
  have harea : 4 ^ k * p ≤ b ^ e :=
    (Nat.mul_le_mul hfour hp).trans ((pow_add b 4 κ).symm.trans_le (hle _ (by omega)))
  have hconst : 16 ≤ b ^ e := (show 16 ≤ (2 : ℕ) ^ 12 by decide).trans
    ((Nat.pow_le_pow_left hb 12).trans (hle _ (by omega)))
  have hB : addressBudget n p k (3 + 3 * (n * n)) 3 (3 + n * n)
      (3 + 2 * (n * n)) ≤ 480 * b ^ e := by
    unfold addressBudget
    nlinarith only [hN2, hN3, hnE, hkE, hpE, hfourE, htwoE, harea, hconst]
  have hmag : 2 * (p + 4) * 16 ^ k ≤ b ^ e := by
    calc
      _ ≤ (10 * b ^ κ) * b ^ 8 := Nat.mul_le_mul (by omega) hsixteen
      _ = 10 * b ^ (κ + 8) := by rw [pow_add]; ring
      _ ≤ b ^ 4 * b ^ (κ + 8) :=
        Nat.mul_le_mul_right _ ((show 10 ≤ (2 : ℕ) ^ 4 by decide).trans (Nat.pow_le_pow_left hb 4))
      _ = b ^ e := (pow_add b 4 (κ + 8)).symm.trans (congrArg _ (by omega))
  calc
    envelope n p A ≤ 485 * b ^ e := by
      unfold envelope magnitudeBudget
      change addressBudget n p k (3 + 3 * (n * n)) 3 (3 + n * n)
        (3 + 2 * (n * n)) + (A + p + 2 * (p + 4) * 16 ^ k + 1) + 1 ≤ _
      omega
    _ ≤ b ^ 9 * b ^ e :=
      Nat.mul_le_mul_right _ ((show 485 ≤ (2 : ℕ) ^ 9 by decide).trans (Nat.pow_le_pow_left hb 9))
    _ = b ^ (κ + 21) := (pow_add b 9 e).symm.trans (congrArg _ (by omega))

/-- Polynomial original moduli and weights give a positive logarithmic physical threshold,
including input fit and both signed-kernel extension bits. Empty matrices are included. -/
theorem admissionWidth_le_log {n p A κ : ℕ}
    (hp : p ≤ (n + 2) ^ κ) (hA : A ≤ (n + 2) ^ κ) :
    admissionWidth n p A ≤ (κ + 24) * Nat.clog 2 (n + 2) := by
  have hpow := (envelope_le_pow hp hA).trans
    (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) (n + 2)) (κ + 21))
  rw [← pow_mul] at hpow
  have hc := Nat.clog_le_of_le_pow hpow
  have hpos : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by decide) (by omega)
  unfold admissionWidth
  nlinarith only [hc, hpos]

/-- The same original hypotheses bound words and memory support by one polynomial independent
of the admitted physical width. -/
theorem wordBound_le_pow {n p A κ : ℕ}
    (hp : p ≤ (n + 2) ^ κ) (hA : A ≤ (n + 2) ^ κ) :
    wordBound n p A ≤ (n + 2) ^ (κ + 25) := by
  have hc : 16 ≤ (n + 2) ^ 4 := (show 16 ≤ (2 : ℕ) ^ 4 by decide).trans
    (Nat.pow_le_pow_left (by omega : 2 ≤ n + 2) 4)
  calc
    _ ≤ (n + 2) ^ 4 * (n + 2) ^ (κ + 21) := Nat.mul_le_mul hc (envelope_le_pow hp hA)
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- Every actual prefix at any sufficiently wide source-regime width has polynomial words
and support, not merely a bound by that physical width's own word universe. -/
theorem bounded_reachable_polynomial {W n p A κ : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hp0 : 0 < p)
    (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hp : p ≤ (n + 2) ^ κ) (hA : A ≤ (n + 2) ^ κ)
    (hW : (κ + 24) * Nat.clog 2 (n + 2) ≤ W)
    (s : State 128) (steps : ℕ)
    (hr : Runs W (entryProgram.program Reg.result) (State.init (inputWords n p values)) s steps) :
    (∀ i, s.data.regs i < (n + 2) ^ (κ + 25)) ∧
      (∀ a, s.data.mem a < (n + 2) ^ (κ + 25)) ∧
      ∀ a, (n + 2) ^ (κ + 25) ≤ a → s.data.mem a = 0 := by
  obtain ⟨regs, memory, support⟩ := bounded_reachable values hlen hp0 hv
    ((admissionWidth_le_log hp hA).trans hW) s steps hr
  have hb := wordBound_le_pow hp hA
  exact ⟨fun i => (regs i).trans_le hb, fun a => (memory a).trans_le hb,
    fun a ha => support a (hb.trans ha)⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
