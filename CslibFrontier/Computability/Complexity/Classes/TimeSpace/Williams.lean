/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Time
public import CslibFrontier.Computability.Complexity.Classes.Space.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DriverComputable
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DriverBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import Mathlib.Data.Nat.Sqrt

/-!
# Williams's square-root-space simulation of deterministic time

Theorem 1.1 of [Williams2025], version 1 (February 25, 2025), states that every multitape time
bound at least the input length admits a deterministic square-root-time-log-time space
simulation. Here both classes use binary multitape machines and arbitrary injective input
encodings. Their bounds allow fixed multiplicative and additive constants. The displayed natural
bound uses `Nat.sqrt (t n * (Nat.log2 (t n) + 1))`, with the added one making the small-input
convention explicit. The input is read-only; space counts visited work-tape cells.

The simulator scans its input and guesses its own time bounds. No time-constructibility or
monotonicity assumption is made on `t`. The supplied source clock is only a proof witness.
Internally, the library uses a fixed-fan-in
three-window block tree and signed masking over a selected prime field; these implementation
choices do not restrict the deterministic source machines covered by the class inclusion.
-/

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM
open _root_.Turing.MultiTapePTM.BlockComputation

private theorem affine_max_product_le (c₁ c₂ : ℕ) : ∃ K, ∀ N x : ℕ, N ≤ x →
    max (N + 1) (c₁ * x + c₂) * (max (N + 1) (c₁ * x + c₂)).size ≤
      K * (x * (Nat.log2 x + 1) + 1) := by
  let a := c₁ + c₂ + 2
  refine ⟨2 * a * (a.size + 2), fun N x hN => ?_⟩
  let y := max (N + 1) (c₁ * x + c₂)
  have hy : y ≤ a * (x + 1) := by
    apply max_le <;> dsimp only [a] <;> nlinarith
  have hsize := (Nat.size_le_size hy).trans (Nat.size_mul_le a (x + 1))
  have hsucc : (x + 1).size ≤ x.size + 1 := Nat.size_le.mpr <| by
    rw [pow_succ]
    have := Nat.lt_size_self x
    omega
  have hxsize : x.size ≤ Nat.log2 x + 1 := by
    simpa only [length_encNat_eq_size] using length_encNat_le_log2 (j := x) le_rfl
  have hmul := Nat.mul_le_mul hy (show y.size ≤ (a.size + 2) * (Nat.log2 x + 1) by nlinarith)
  have hround : (x + 1) * (Nat.log2 x + 1) ≤ 2 * (x * (Nat.log2 x + 1) + 1) := by
    rcases eq_or_ne x 0 with rfl | hx
    · decide
    · nlinarith [Nat.mul_le_mul_right (Nat.log2 x + 1) (show x + 1 ≤ 2 * x by omega)]
  have hscale := Nat.mul_le_mul_left (a * (a.size + 2)) hround
  dsimp only [y] at hmul ⊢
  nlinarith

private theorem le_affine_sqrt_of_sq_le {x y C : ℕ} (h : x ^ 2 ≤ C * (y + 1)) :
    x ≤ (C + 1) * Nat.sqrt y + (C + 1) := by
  have hsq : x ^ 2 ≤ ((C + 1) * (Nat.sqrt y + 1)) ^ 2 :=
    calc _ ≤ C * (y + 1) := h
      _ ≤ (C + 1) ^ 2 * (Nat.sqrt y + 1) ^ 2 :=
        Nat.mul_le_mul (by nlinarith)
          (by nlinarith [Nat.sqrt_le_add y])
      _ = _ := by ring
  linarith [(Nat.pow_le_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).mp hsq]

/-- The complete driver absorbs an arbitrary affine source clock into the conventional
square-root-time-log-time resource, including its input-length scan. -/
theorem williams_driver_space_le (k s : ℕ) (Q : Type) (c₁ c₂ : ℕ) :
    ∃ C, ∀ N x : ℕ, N ≤ x →
      Driver.space k (InitializedEvaluator.scheduleAllowance k s Q) BalancedParameters.parameters
        N (c₁ * x + c₂) ≤ C * Nat.sqrt (x * (Nat.log2 x + 1)) + C := by
  obtain ⟨c, hc⟩ := Driver.space_sq_le k s Q
  obtain ⟨K, hK⟩ := affine_max_product_le c₁ c₂
  refine ⟨c * K + 1, fun N x hN => ?_⟩
  have h := (hc N (c₁ * x + c₂)).trans (Nat.mul_le_mul_left c (hK N x hN))
  rw [← Nat.mul_assoc] at h
  exact le_affine_sqrt_of_sq_le h

/-- Williams's deterministic time-to-space inclusion, for every injective input encoding.
This is Theorem 1.1 of [Williams2025], version 1, in the library's affine-bound multitape
classes. The binary logarithm and natural square root differ from the paper's asymptotic
notation only by fixed constants and the explicit small-input convention. -/
theorem DTIME_subset_DSPACE_sqrt {α : Type*} (enc : α ↪ List Bool) (t : ℕ → ℕ)
    (ht : ∀ n, n ≤ t n) :
    DTIME enc t ⊆ DSPACE enc (fun n => Nat.sqrt (t n * (Nat.log2 (t n) + 1))) := by
  classical
  rintro A ⟨c₁, c₂, sourceSpace, k, Q, hfinite, M, hM⟩
  let : Finite Q := hfinite
  let : Fintype Q := Fintype.ofFinite Q
  let e : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  -- The range subtype is small even when the encoded instance type lives in a higher universe.
  let Input := Set.range enc
  let inputEncoding : Input ↪ List Bool := ⟨Subtype.val, Subtype.val_injective⟩
  let clock : Input → ℕ := fun word => c₁ * t word.val.length + c₂
  have hclock (word : Input) :
      (M.runFrom (Turing.Cfg.init M.q₀ (inputEncoding word)) (clock word)).Halted := by
    obtain ⟨a, ha⟩ := word.property
    change (M.runFrom (Turing.Cfg.init M.q₀ word.val) (c₁ * t word.val.length + c₂)).Halted
    rw [← ha]
    simpa only [Turing.MultiTapeNTM.initCfg] using ((hM a).runFrom_of_le le_rfl).1
  obtain ⟨simTime, simFactor, k', Q', hfinite', simulator, hsim⟩ :=
    Driver.computableInSpace_decision (InitializedEvaluator.scheduleEvaluator_correct M e)
      BalancedParameters.parameters inputEncoding clock hclock
  obtain ⟨C, hC⟩ := williams_driver_space_le k (Fintype.card Q) Q c₁ c₂
  refine mem_DSPACE_iff.mpr ⟨simFactor * C, simFactor * C, fun a => simTime ⟨enc a, ⟨a, rfl⟩⟩,
    k', Q', hfinite', simulator, fun a => ?_⟩
  have h := hsim ⟨enc a, ⟨a, rfl⟩⟩
  have hsource := (hM a).runFrom_of_le le_rfl
  simp only [Turing.MultiTapeNTM.initCfg] at hsource
  have hout : decide ((M.runFrom (Turing.Cfg.init M.q₀ (enc a))
      (c₁ * t (enc a).length + c₂)).output = [true]) = indicator A a := by
    rw [hsource.2]
    cases indicator A a <;> rfl
  have hcompute : simulator.Computes (enc a)
      [decide ((M.runFrom (Turing.Cfg.init M.q₀ (enc a))
        (c₁ * t (enc a).length + c₂)).output = [true])] := h.1
  rw [hout] at hcompute
  refine ⟨hcompute, h.2.1, h.2.2.mono ?_⟩
  dsimp only [inputEncoding, clock]
  simpa only [Function.Embedding.coeFn_mk, Nat.mul_add, ← Nat.mul_assoc] using
    Nat.mul_le_mul_left simFactor (hC (enc a).length (t (enc a).length) (ht _))

end Cslib.Complexity
