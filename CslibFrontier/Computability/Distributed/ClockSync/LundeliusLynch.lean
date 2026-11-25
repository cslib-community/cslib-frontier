/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.ClockSync.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Lockstep drift-free clock-synchronization step bounds

This module proves a **synchronous lockstep, drift-free `R`-round step** towards the
`((n - 1) / n) * (d_max - d_min)` clock-synchronization bound of
[Lundelius and Lynch][LundeliusLynch1984], and is **not** the cited paper's general asynchronous
event-driven lower bound (which remains open in
[#7202](https://github.com/cslib-community/cslib-frontier/issues/7202)).

Over a complete network of `n = Fintype.card P` processes with unit-rate drift-free hardware clocks
and message transit delays in `[d_min, d_max]` (`d_min ≤ d_max`), we show for deterministic
fixed-`R`-round lockstep protocols (`LockstepProtocol P K R`) that the minimax worst-case clock
skew is `((n - 1) / n) * (d_max - d_min)` (for `n = 1`, `0 ≤ γ` holds trivially from `|x - x| = 0`):

* **Lockstep lower-bound step (`lockstepClockSync_lower_bound`):** For `n = 1`, `0 ≤ γ` is
  immediate; for `n ≥ 2`, starting from `(c₀, δ₀)` with `c₀ ≡ 0` and `δ₀ r i j = d_min` for
  `i ≤ j`, `d_max` for `i > j` under an enumeration `P ≃ Fin n`, applying `syncOffset_shift_eq`
  across the `n - 1` prefix shifts `s_m i = u` for `i < m` (`u = d_max - d_min`) keeps every
  shifted delay inside `{d_min, d_max} ⊆ [d_min, d_max]`. Summing the `n - 1` adjacent bounds from
  the shifted executions together with the wrap-around bound from the base execution telescopes all
  protocol adjustments to zero, yielding `(n - 1) * u ≤ n * γ` for every `R`-round
  `LockstepProtocol P K R` achieving skew `γ`.
* **1-round lockstep averaging step (`lockstepClockAvg`, `lockstepClockAvg_achievesSkew`):** In 1
  lockstep round, each process broadcasts at local clock reading `0` and sets its adjustment to the
  average of `estDiff d_min d_max p arrival q` over all `q : P`. For any `p ≠ q`, the two endpoint
  terms `r = p` and `r = q` contribute error at most `u / 2` each while the remaining `n - 2` terms
  contribute at most `u` each, achieving lockstep skew `((n - 1) / n) * u`.
* **Lockstep minimax step (`exists_achievesLockstepSkew_iff`):** Across all round counts `R`, a
  `LockstepProtocol P K R` achieves skew `γ` if and only if `((n - 1) / n) * (d_max - d_min) ≤ γ`;
  within the lockstep `R`-round model, multi-round communication (`R > 1`) cannot improve upon
  1-round `lockstepClockAvg`.

## Main definitions

* `Cslib.Distributed.ClockSync.lockstepClockAvg`: 1-round lockstep all-to-all midpoint-delay
  averaging protocol on drift-free clocks.

## Main results

* `Cslib.Distributed.ClockSync.lockstepClockSync_lower_bound`: lockstep `R`-round step towards
  [Lundelius and Lynch][LundeliusLynch1984] proving
  `((Fintype.card P - 1 : K) / Fintype.card P) * (d_max - d_min) ≤ γ` (`#7202`).
* `Cslib.Distributed.ClockSync.lockstepClockAvg_achievesSkew`: `lockstepClockAvg` achieves lockstep
  skew `((Fintype.card P - 1 : K) / Fintype.card P) * (d_max - d_min)` in 1 round.
* `Cslib.Distributed.ClockSync.exists_achievesLockstepSkew_iff`: minimax skew characterization
  within the synchronous lockstep `R`-round model (`#7202`).

## References

* [J. Lundelius, N. Lynch, *An upper and lower bound for clock synchronization*][LundeliusLynch1984]
-/

public section

namespace Cslib.Distributed.ClockSync

universe u v

/-! ### Prefix-shifted executions and the lockstep `(1 - 1 / n) * (d_max - d_min)` lower bound -/

private theorem validDelays_prefixShift {P : Type u} {K : Type v}
    [AddCommGroup K] [LinearOrder K] {n : ℕ} (e : P ≃ Fin n)
    {d_min d_max : K} (hd : d_min ≤ d_max) (m : ℕ) :
    ValidDelays d_min d_max
      (shiftDelays (fun _ p q => if e p ≤ e q then d_min else d_max)
        (fun p => if (e p).val < m then d_max - d_min else 0)) := by
  intro r p q
  dsimp only [shiftDelays]
  by_cases hp : (e p).val < m <;> by_cases hq : (e q).val < m
  · simp only [hp, hq, ↓reduceIte, add_sub_cancel_right]
    split_ifs
    · exact ⟨le_rfl, hd⟩
    · exact ⟨hd, le_rfl⟩
  · have hpq : e p ≤ e q := Fin.le_def.mpr (by omega)
    simp only [hp, hq, hpq, ↓reduceIte, sub_zero, add_sub_cancel]
    exact ⟨hd, le_rfl⟩
  · have hpq : ¬ e p ≤ e q := by rw [Fin.le_def]; omega
    simp only [hp, hq, hpq, ↓reduceIte, add_zero, sub_sub_cancel]
    exact ⟨le_rfl, hd⟩
  · simp only [hp, hq, ↓reduceIte, sub_zero, add_zero]
    split_ifs
    · exact ⟨le_rfl, hd⟩
    · exact ⟨hd, le_rfl⟩

/-- A synchronous lockstep, drift-free `R`-round step towards
[Lundelius and Lynch][LundeliusLynch1984], and not the cited asynchronous event-driven lower bound
(`#7202`): any deterministic `R`-round `LockstepProtocol P K R` achieving worst-case skew `γ` on a
nonempty finite complete network `P` against transit delays in `[d_min, d_max]` (`d_min ≤ d_max`)
satisfies `((Fintype.card P - 1 : K) / Fintype.card P) * (d_max - d_min) ≤ γ` (for
`Fintype.card P = 1`, `0 ≤ γ` follows immediately from `|x - x| = 0`; the prefix-shift telescoping
argument applies to `2 ≤ Fintype.card P`). -/
theorem lockstepClockSync_lower_bound {P : Type u} [Fintype P] [Nonempty P]
    {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {R : ℕ} {π : LockstepProtocol P K R} {d_min d_max γ : K}
    (hd : d_min ≤ d_max) (hπ : AchievesLockstepSkew π d_min d_max γ) :
    ((Fintype.card P - 1 : K) / Fintype.card P) * (d_max - d_min) ≤ γ := by
  set n := Fintype.card P
  have hn_pos : 1 ≤ n := Fintype.card_pos
  have hnK : (0 : K) < n := Nat.cast_pos.mpr hn_pos
  by_cases hn1 : n = 1
  · obtain ⟨p₀⟩ := ‹Nonempty P›
    have h0 := hπ (fun _ => 0) (fun _ _ _ => d_min) (fun _ _ _ => ⟨le_rfl, hd⟩) p₀ p₀
    simpa only [hn1, Nat.cast_one, sub_self, zero_div, zero_mul, abs_zero] using h0
  · have hn2 : 2 ≤ n := by omega
    let e : P ≃ Fin n := Fintype.equivFin P
    let c₀ : P → K := fun _ => 0
    let δ₀ : ℕ → P → P → K := fun _ p q => if e p ≤ e q then d_min else d_max
    let u : K := d_max - d_min
    let s : ℕ → P → K := fun m p => if (e p).val < m then u else 0
    let z : ℕ → K := fun k => if hk : k < n then π.syncOffset c₀ δ₀ (e.symm ⟨k, hk⟩) else 0
    have hstep : ∀ k ∈ Finset.range (n - 1), u + (z k - z (k + 1)) ≤ γ := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hk0 : k < n := by omega
      have hk1 : k + 1 < n := by omega
      let p₀ := e.symm ⟨k, hk0⟩
      let p₁ := e.symm ⟨k + 1, hk1⟩
      have hskew := hπ (shiftOffsets c₀ (s (k + 1))) (shiftDelays δ₀ (s (k + 1)))
        (validDelays_prefixShift e hd (k + 1)) p₀ p₁
      simp only [syncOffset_shift_eq, s, p₀, p₁, Equiv.apply_symm_apply, lt_add_one,
        lt_self_iff_false, ↓reduceIte, add_zero] at hskew
      simp only [z, hk0, hk1, ↓reduceDIte]
      linarith [(le_abs_self _).trans hskew]
    have hsum := Finset.sum_le_sum hstep
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, nsmul_eq_mul, Finset.sum_range_sub' z (n - 1)] at hsum
    have hbase : z (n - 1) - z 0 ≤ γ := by
      have hδ₀ : ValidDelays d_min d_max δ₀ := fun _ p q => by
        dsimp only [δ₀]
        split_ifs
        exacts [⟨le_rfl, hd⟩, ⟨hd, le_rfl⟩]
      have h0 := hπ c₀ δ₀ hδ₀ (e.symm ⟨n - 1, by omega⟩) (e.symm ⟨0, by omega⟩)
      simp only [z, show n - 1 < n by omega, show 0 < n by omega, ↓reduceDIte]
      exact (le_abs_self _).trans h0
    rw [Nat.cast_sub hn_pos, Nat.cast_one] at hsum
    rw [div_mul_eq_mul_div, div_le_iff₀ hnK]
    linarith

/-! ### 1-round lockstep averaging upper bound and lockstep minimax step -/

/-- 1-round lockstep all-to-all midpoint-delay averaging protocol on drift-free clocks (a
synchronous lockstep step after [Lundelius and Lynch][LundeliusLynch1984], `#7202`): every process
broadcasts at local clock reading `0` and sets its clock adjustment to
`(∑ q : P, estDiff d_min d_max p v.lastArrival q) / |P|`. -/
@[expose] def lockstepClockAvg {P : Type u} [Fintype P] [DecidableEq P]
    {K : Type v} [Field K] (d_min d_max : K) : LockstepProtocol P K 1 where
  sendTime _ _ _ _ := 0
  adjust p v := (∑ q : P, estDiff d_min d_max p v.lastArrival q) / Fintype.card P

/-- A synchronous lockstep, drift-free 1-round step after
[Lundelius and Lynch][LundeliusLynch1984], and not the cited asynchronous event-driven result
(`#7202`): `lockstepClockAvg` achieves worst-case lockstep clock skew
`((Fintype.card P - 1 : K) / Fintype.card P) * (d_max - d_min)` whenever `d_min ≤ d_max`. -/
theorem lockstepClockAvg_achievesSkew {P : Type u} [Fintype P] [DecidableEq P] [Nonempty P]
    {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {d_min d_max : K} (hd : d_min ≤ d_max) :
    AchievesLockstepSkew (lockstepClockAvg (P := P) d_min d_max) d_min d_max
      (((Fintype.card P - 1 : K) / Fintype.card P) * (d_max - d_min)) := by
  intro c δ hδ p q
  set n := Fintype.card P
  have hn_pos : 1 ≤ n := Fintype.card_pos
  have hnK_pos : (0 : K) < n := Nat.cast_pos.mpr hn_pos
  have hnK_ne : (n : K) ≠ 0 := ne_of_gt hnK_pos
  set u : K := d_max - d_min
  by_cases hpq : p = q
  · subst hpq
    rw [sub_self, abs_zero]
    exact mul_nonneg (div_nonneg (sub_nonneg.mpr (Nat.one_le_cast.mpr hn_pos)) hnK_pos.le)
      (sub_nonneg.mpr hd)
  · let recv : P → P → K := fun x r => arrivalReading c δ 0 r x 0
    let xEst : P → P → K := fun x r => c x + estDiff d_min d_max x (recv x) r
    have hsync : ∀ x : P,
        (lockstepClockAvg d_min d_max).syncOffset c δ x = (∑ r : P, xEst x r) / n := by
      intro x
      have hsum : ∑ r : P, xEst x r = n * c x + ∑ r : P, estDiff d_min d_max x (recv x) r := by
        simp only [xEst, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          n]
      dsimp only [LockstepProtocol.syncOffset, LockstepProtocol.adj, lockstepClockAvg,
        LockstepProtocol.localView, LocalView.lastArrival, n]
      rw [hsum, add_div, mul_div_cancel_left₀ (c x) hnK_ne]
      rfl
    have herr : ∀ x r : P, |xEst x r - c r| ≤ u / 2 := fun x r =>
      abs_add_estDiff_sub_le hd c x r (recv x)
        (fun _ => by simp only [recv, arrivalReading, zero_add])
        (fun _ => (hδ 0 r x).1) (fun _ => (hδ 0 r x).2)
    have hself : ∀ x : P, xEst x x = c x := fun x => by
      simp only [xEst, estDiff, ↓reduceIte, add_zero]
    have hp_term : |xEst p p - xEst q p| ≤ u / 2 := by
      rw [hself p, abs_sub_comm]
      exact herr q p
    have hq_term : |xEst p q - xEst q q| ≤ u / 2 := by
      rw [hself q]
      exact herr p q
    have hq_mem : q ∈ (Finset.univ.erase p : Finset P) :=
      Finset.mem_erase.mpr ⟨Ne.symm hpq, Finset.mem_univ q⟩
    let rest : Finset P := (Finset.univ.erase p).erase q
    have hcard_rest : rest.card = n - 2 := by
      have hc1 : (Finset.univ.erase p : Finset P).card = n - 1 :=
        Finset.card_erase_of_mem (Finset.mem_univ p)
      rw [Finset.card_erase_of_mem hq_mem, hc1]
      omega
    have hn2 : 2 ≤ n := Fintype.one_lt_card_iff.mpr ⟨p, q, hpq⟩
    have hsum_bound : ∑ r : P, |xEst p r - xEst q r| ≤ ((n : K) - 1) * u := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), ← Finset.add_sum_erase _ _ hq_mem]
      have hrest_sum := Finset.sum_le_card_nsmul rest (fun r => |xEst p r - xEst q r|) u
        fun r _ => by linarith [abs_sub_le (xEst p r) (c r) (xEst q r),
          abs_sub_comm (c r) (xEst q r), herr p r, herr q r]
      rw [hcard_rest, nsmul_eq_mul, Nat.cast_sub hn2, Nat.cast_ofNat] at hrest_sum
      linarith
    rw [hsync p, hsync q, ← sub_div, abs_div, abs_of_pos hnK_pos, ← Finset.sum_sub_distrib,
      div_mul_eq_mul_div, div_le_div_iff_of_pos_right hnK_pos]
    exact (Finset.abs_sum_le_sum_abs _ _).trans hsum_bound

/-- A synchronous lockstep, drift-free `R`-round minimax step towards
[Lundelius and Lynch][LundeliusLynch1984], and not a characterization over asynchronous
event-driven protocols (`#7202`): there exists a round count `R` and a deterministic
`LockstepProtocol P K R` achieving worst-case clock skew `γ` on `P` against transit delays in
`[d_min, d_max]` (`d_min ≤ d_max`) if and only if
`((Fintype.card P - 1 : K) / Fintype.card P) * (d_max - d_min) ≤ γ` (trivial `0 ≤ γ` for
`Fintype.card P = 1`; `lockstepClockSync_lower_bound` and `lockstepClockAvg_achievesSkew` for
`2 ≤ Fintype.card P`). -/
theorem exists_achievesLockstepSkew_iff {P : Type u} [Fintype P] [Nonempty P]
    {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {d_min d_max γ : K} (hd : d_min ≤ d_max) :
    (∃ (R : ℕ) (π : LockstepProtocol P K R), AchievesLockstepSkew π d_min d_max γ) ↔
      ((Fintype.card P - 1 : K) / Fintype.card P) * (d_max - d_min) ≤ γ := by
  constructor
  · rintro ⟨R, π, hπ⟩
    exact lockstepClockSync_lower_bound hd hπ
  · intro hγ
    let _ := Classical.decEq P
    exact ⟨1, lockstepClockAvg d_min d_max, (lockstepClockAvg_achievesSkew hd).mono hγ⟩

end Cslib.Distributed.ClockSync
