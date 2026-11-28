/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Time
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Quantitative deterministic time transfer

The cost of a many-one reduction is governed both by its construction time and by its encoded
output length. A reduction of degrees `a` and `b` transfers a source time exclusion at degree
`h` to degree `d` on the target when `a < h` and `b * d < h`. Fixed powers of a logarithm
are absorbed by the strict inequalities. The proofs use the existing native multitape model.

For a fixed positive integer degree, linear output length is equivalent to charging the target
clock at the same degree, provided construction fits that clock. The existing machine-layer
`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.comp` accounts for the exact intermediate-copy
cost of `4m + 9` transitions for `m` emitted bits. The class-level transfer uses the plain
`Turing.MultiTapeTM.ComputableInO.comp` interface via `preimage_mem_DTIME`.

## Main definitions

* `realPowerClock` is the natural clock obtained from a real exponent.
* `TimedReductionDegrees` records machine and encoded-length envelopes separately.

## Main results

* `timedReductionDegrees_of_polylog` and `transfer_time_exclusion` give the strict transfer.
* `clockBudget_iff` characterizes same-degree clock budgets.
* `target_not_mem_DTIME_of_clockPreserving` transfers the same native time exclusion.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
  defines deterministic time (Definition 1.12). The budget lemmas use Frontier’s native model.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Filter Asymptotics

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}

/-- The natural-valued clock obtained by rounding down the real power of the length plus one. -/
@[expose] noncomputable def realPowerClock (h : ℝ) (n : Nat) : Nat := ⌊((n : ℝ) + 1) ^ h⌋₊

/-- The bounds charge the actual emitted bits. Constants may depend on the
chosen reduction and on the slack in the exponent. -/
@[expose] def TimedReductionDegrees (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (L : Set α) (B : Set β) (a b : ℝ) : Prop :=
  ∃ (f : α → β) (T S : α → ℕ),
    (∀ x, x ∈ L ↔ f x ∈ B) ∧ ComputableInO f encA encB T S ∧
    ∀ ε : ℝ, 0 < ε → ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧
      ∀ x, (T x : ℝ) ≤ A * (((encA x).length : ℝ) + 1) ^ (a + ε) ∧
        ((encB (f x)).length : ℝ) + 1 ≤ D * (((encA x).length : ℝ) + 1) ^ (b + ε)

/-- Absorb fixed powers of a logarithm into any positive exponent slack. The
successor offset makes this a bound on every input length, including zero. -/
private theorem logPower_budget (r : Nat) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Nat,
      (Real.log ((n : ℝ) + 2)) ^ r ≤ C * ((n : ℝ) + 1) ^ ε := by
  have hlo : (fun x : ℝ => Real.log x ^ r) =O[atTop] fun x => x ^ ε := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (s := ε) (r : ℝ) hε).isBigO
  have castTop : Tendsto (fun n : Nat => (n : ℝ) + 2) atTop atTop := by
    refine tendsto_atTop.2 fun x => ?_
    obtain ⟨N, hN⟩ := exists_nat_ge x
    exact eventually_atTop.2 ⟨N, fun n hn => by
      have cast : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith⟩
  obtain ⟨D, hD, hEventually⟩ := (hlo.comp_tendsto castTop).exists_pos
  obtain ⟨N, hN⟩ := eventually_atTop.mp hEventually.bound
  let initial := ((Finset.range N).sum fun n =>
    (Real.log ((n : ℝ) + 2)) ^ r)
  have nonneg (n : Nat) : 0 ≤ (Real.log ((n : ℝ) + 2)) ^ r := by
    exact pow_nonneg (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)) _
  have hInit : 0 ≤ initial := Finset.sum_nonneg fun n _ => nonneg n
  refine ⟨D * (2 : ℝ) ^ ε + initial,
    add_nonneg (mul_nonneg hD.le (by positivity)) hInit, fun n => ?_⟩
  have hx : 1 ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hp : 1 ≤ ((n : ℝ) + 1) ^ ε := Real.one_le_rpow hx hε.le
  by_cases h : N ≤ n
  · have bound := hN n h
    dsimp only [Function.comp_apply] at bound
    rw [Real.norm_of_nonneg (nonneg n), Real.norm_of_nonneg (by positivity)] at bound
    have scale : ((n : ℝ) + 2) ^ ε ≤ (2 : ℝ) ^ ε * ((n : ℝ) + 1) ^ ε := by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)]
      exact Real.rpow_le_rpow (by positivity) (by linarith) hε.le
    calc
      _ ≤ D * ((2 : ℝ) ^ ε * ((n : ℝ) + 1) ^ ε) :=
        bound.trans (mul_le_mul_of_nonneg_left scale hD.le)
      _ ≤ _ := by nlinarith [mul_nonneg hInit (show 0 ≤ ((n : ℝ) + 1) ^ ε by positivity)]
  · have bound : (Real.log ((n : ℝ) + 2)) ^ r ≤ initial :=
      Finset.single_le_sum (f := fun (m : Nat) => (Real.log ((m : ℝ) + 2)) ^ r)
        (fun m _ => nonneg m) (Finset.mem_range.mpr (by omega))
    calc
      _ ≤ initial := bound
      _ ≤ initial * ((n : ℝ) + 1) ^ ε := by simpa using mul_le_mul_of_nonneg_left hp hInit
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (mul_nonneg hD.le (by positivity))) (by positivity)

/-- Machine and output bounds with independent logarithmic factors yield the
arbitrarily small exponent slack consumed by the transfer theorem. -/
theorem timedReductionDegrees_of_polylog {L : Set α} {B : Set β} {a b A D : ℝ}
    {p q : Nat} {f : α → β} {T S : α → ℕ}
    (hA : 0 ≤ A) (hD : 0 ≤ D)
    (correct : ∀ x, x ∈ L ↔ f x ∈ B)
    (machine : ComputableInO f encA encB T S)
    (bounds : ∀ x,
      (T x : ℝ) ≤ A * (((encA x).length : ℝ) + 1) ^ a * (Real.log (((encA x).length : ℝ) + 2)) ^ p ∧
      ((encB (f x)).length : ℝ) + 1 ≤
        D * (((encA x).length : ℝ) + 1) ^ b * (Real.log (((encA x).length : ℝ) + 2)) ^ q) :
    TimedReductionDegrees encA encB L B a b := by
  refine ⟨f, T, S, correct, machine, fun ε hε => ?_⟩
  obtain ⟨C, hC, hp⟩ := logPower_budget p ε hε
  obtain ⟨K, hK, hq⟩ := logPower_budget q ε hε
  have absorb (n : ℕ) (u v z e : ℝ) (hu : 0 ≤ u)
      (bound : z ≤ v * ((n : ℝ) + 1) ^ ε) :
      u * ((n : ℝ) + 1) ^ e * z ≤ (u * v) * ((n : ℝ) + 1) ^ (e + ε) := by
    rw [Real.rpow_add (by positivity : 0 < (n : ℝ) + 1)]
    calc
      _ ≤ u * ((n : ℝ) + 1) ^ e * (v * ((n : ℝ) + 1) ^ ε) :=
        mul_le_mul_of_nonneg_left bound (mul_nonneg hu (by positivity))
      _ = _ := by ring
  refine ⟨A * C, D * K, mul_nonneg hA hC, mul_nonneg hD hK, fun x => ?_⟩
  obtain ⟨ht, hm⟩ := bounds x
  exact ⟨ht.trans (absorb (encA x).length A C _ a hA (hp (encA x).length)),
    hm.trans (absorb (encA x).length D K _ b hD (hq (encA x).length))⟩

/-- Reduce with the exact encoded-length clock and Frontier's native
materializing composition. Its linear output-copy cost is absorbed since d ≥ 1. -/
theorem transfer_time_exclusion {L : Set α} {B : Set β} {a b h d : ℝ}
    (hd : 1 ≤ d) (ha : a < h) (hb : b * d < h)
    (reduction : TimedReductionDegrees encA encB L B a b)
    (hard : L ∉ DTIME encA (realPowerClock h)) :
    B ∉ DTIME encB (realPowerClock d) := by
  obtain ⟨f, T, S, correct, machine, budget⟩ := reduction
  let δ : ℝ := min (h - a) (h - b * d)
  let ε : ℝ := δ / (2 * (d + 1))
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hε : 0 < ε := div_pos hδ (by positivity)
  have hmul : ε * (2 * (d + 1)) = δ := by
    dsimp [ε]
    exact div_mul_cancel₀ _ (by positivity)
  have hx : a + ε ≤ h := by
    have := min_le_left (h - a) (h - b * d)
    dsimp [δ] at hmul
    nlinarith
  have hy : (b + ε) * d ≤ h := by
    have := min_le_right (h - a) (h - b * d)
    dsimp [δ] at hmul
    nlinarith
  obtain ⟨A, D, hA, hD, bnd⟩ := budget ε hε
  obtain ⟨C, hC⟩ := exists_nat_ge (A + D ^ d)
  intro upper
  have eq : f ⁻¹' B = L := Set.ext fun x => (correct x).symm
  apply hard
  rw [← eq]
  apply preimage_mem_DTIME (C := C) upper machine
  intro x
  let n : ℝ := ((encA x).length : ℝ) + 1
  have hn : 1 ≤ n := by
    dsimp [n]
    have := Nat.cast_nonneg (α := ℝ) (encA x).length
    linarith
  obtain ⟨ht, hm⟩ := bnd x
  change (T x : ℝ) ≤ A * n ^ (a + ε) at ht
  change ((encB (f x)).length : ℝ) + 1 ≤ D * n ^ (b + ε) at hm
  have ht' := ht.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn hx) hA)
  have hm' := Real.rpow_le_rpow (by positivity : 0 ≤ ((encB (f x)).length : ℝ) + 1) hm
    (by linarith : 0 ≤ d)
  rw [Real.mul_rpow hD (by positivity), ← Real.rpow_mul (by linarith : 0 ≤ n)] at hm'
  have hm'' := hm'.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn hy)
    (Real.rpow_nonneg hD _))
  have targetFloor :
      (realPowerClock d (encB (f x)).length : ℝ) ≤ (((encB (f x)).length : ℝ) + 1) ^ d :=
    Nat.floor_le (by positivity)
  have hfloor : n ^ h ≤ (realPowerClock h (encA x).length : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  have charge : (T x : ℝ) + (realPowerClock d (encB (f x)).length : ℝ) ≤
      (C : ℝ) * (realPowerClock h (encA x).length : ℝ) + (C : ℝ) := by
    calc
      _ ≤ A * n ^ h + D ^ d * n ^ h := add_le_add ht' (targetFloor.trans hm'')
      _ = (A + D ^ d) * n ^ h := by ring
      _ ≤ (C : ℝ) * n ^ h := mul_le_mul_of_nonneg_right hC (by positivity)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hfloor (show (0 : ℝ) ≤ C by positivity)
        linarith
  exact_mod_cast charge

/-- A single target with common reduction exponents from sources with
unbounded excluded exponents cannot be in deterministic polynomial time. -/
theorem outside_P_of_common_reduction_degrees {B : Set β} {a b : ℝ}
    (family : ∀ h : ℝ, ∃ L : Set α,
      L ∉ DTIME encA (realPowerClock h) ∧ TimedReductionDegrees encA encB L B a b) :
    B ∉ P encB := by
  intro hP
  obtain ⟨d, hd⟩ := mem_P_iff_exists_mem_DTIME.mp hP
  let e := d + 1
  have up : B ∈ DTIME encB (fun n => (n + 1) ^ e) :=
    DTIME_mono (fun n => (Nat.pow_le_pow_left (Nat.le_succ n) _).trans
      (Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_succ d))) hd
  obtain ⟨L, hL, red⟩ := family (max a (b * (e : ℝ)) + 1)
  have clock (n : Nat) : realPowerClock (e : ℝ) n = (n + 1) ^ e := by
    unfold realPowerClock
    rw [Real.rpow_natCast, ← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_pow, Nat.floor_natCast]
  have up' : B ∈ DTIME encB (realPowerClock (e : ℝ)) := by
    simpa only [← clock] using up
  have pos : (1 : ℝ) ≤ e := by exact_mod_cast (show 1 ≤ e by omega)
  exact transfer_time_exclusion pos
    (by linarith [le_max_left a (b * (e : ℝ))])
    (by linarith [le_max_right a (b * (e : ℝ))]) red hL up'

/-- A positive-degree target clock forces linear output growth, even if the
reduction itself is free. The bound is for the length plus one. -/
private theorem clockBudget_length {d C n m t : Nat} (hd : 1 ≤ d)
    (h : t + (m + 1) ^ d ≤ C * (n + 1) ^ d + C) :
    m + 1 ≤ 2 * C * (n + 1) := by
  have hn : 1 ≤ (n + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hC : C ≤ C * (n + 1) ^ d := by simpa using Nat.mul_le_mul_left C hn
  have hp : 2 * C ≤ (2 * C) ^ d := by
    simpa using Nat.pow_le_pow_right (show 0 < 2 * C by
      by_contra! hz
      have : C = 0 := by omega
      subst C
      simp at h) hd
  apply (Nat.pow_le_pow_iff_left (by omega : d ≠ 0)).mp
  rw [mul_pow]
  calc
    (m + 1) ^ d ≤ C * (n + 1) ^ d + C := (Nat.le_add_left _ _).trans h
    _ ≤ 2 * C * (n + 1) ^ d := by rw [Nat.mul_assoc]; omega
    _ ≤ (2 * C) ^ d * (n + 1) ^ d := Nat.mul_le_mul_right _ hp

/-- A linear output and a degree-d construction budget suffice for the charged
clock inequality. This is the hypothesis used by the native composition theorem. -/
theorem clockBudget_iff {α : Type} (n m t : α → Nat) {d : Nat} (hd : 1 ≤ d) :
    (∃ C, ∀ x, t x + (m x + 1) ^ d ≤ C * (n x + 1) ^ d + C) ↔
    (∃ A B, ∀ x, t x ≤ A * (n x + 1) ^ d + A ∧ m x + 1 ≤ B * (n x + 1)) := by
  constructor
  · rintro ⟨C, h⟩
    exact ⟨C, 2 * C, fun x => ⟨(Nat.le_add_right _ _).trans (h x),
      clockBudget_length hd (h x)⟩⟩
  · rintro ⟨A, B, h⟩
    refine ⟨A + B ^ d, fun x => ?_⟩
    obtain ⟨ht, hm⟩ := h x
    have hp := Nat.pow_le_pow_left hm d
    rw [mul_pow] at hp
    calc
      _ ≤ A * (n x + 1) ^ d + A + B ^ d * (n x + 1) ^ d := Nat.add_le_add ht hp
      _ ≤ _ := by rw [Nat.add_mul]; omega

/-- A same-degree construction clock and linear encoded output growth preserve a positive
integer time exclusion under a native deterministic reduction. -/
theorem target_not_mem_DTIME_of_clockPreserving {d A D : ℕ} (hd : 1 ≤ d)
    {L : Set α} {B : Set β} {f : α → β} {T S : α → ℕ}
    (lower : L ∉ DTIME encA (fun n => (n + 1) ^ d))
    (correct : ∀ x, x ∈ L ↔ f x ∈ B)
    (machine : ComputableInO f encA encB T S)
    (resources : ∀ x, T x ≤ A * ((encA x).length + 1) ^ d + A ∧
      (encB (f x)).length + 1 ≤ D * ((encA x).length + 1)) :
    B ∉ DTIME encB (fun n => (n + 1) ^ d) := by
  intro upper
  obtain ⟨C, budget⟩ :=
    (clockBudget_iff (fun x => (encA x).length) (fun x => (encB (f x)).length) T hd).mpr
      ⟨A, D, resources⟩
  have eq : f ⁻¹' B = L := Set.ext fun x => (correct x).symm
  apply lower
  rw [← eq]
  exact preimage_mem_DTIME (C := C) upper machine budget

end Cslib.Complexity
