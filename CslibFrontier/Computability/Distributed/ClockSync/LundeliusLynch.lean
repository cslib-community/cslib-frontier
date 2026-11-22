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
# Tight Lundelius–Lynch bounds for clock synchronization

Over a complete network of `n = Fintype.card P` processes with drift-free hardware clocks and
message transit delays in `[d_min, d_max]` (`d_min ≤ d_max`), this module establishes for the
deterministic synchronous full-information `R`-round model (`Protocol P K R`) that the minimax
worst-case clock skew is *exactly*

`((n - 1) / n) * (d_max - d_min)`,

formalizing the bound of [Lundelius and Lynch][LundeliusLynch1984] (who consider event-driven
deterministic message passing on `n ≥ 2` processes; for `n = 1`, `0 ≤ γ` holds trivially from
`|x - x| = 0`).

* **Lower bound (`lundeliusLynch_lower_bound`):** For `n = 1`, `0 ≤ γ` is immediate; for `n ≥ 2`,
  starting from `(c₀, δ₀)` with `c₀ ≡ 0` and `δ₀ r i j = d_min` for `i ≤ j`, `d_max` for `i > j`
  under an enumeration `P ≃ Fin n`, applying `syncOffset_shift_eq` across the `n - 1` prefix shifts
  `s_m i = u` for `i < m` (`u = d_max - d_min`) keeps every shifted delay inside
  `{d_min, d_max} ⊆ [d_min, d_max]`. Summing the `n - 1` adjacent bounds from the shifted
  executions together with the wrap-around bound from the base execution telescopes all protocol
  adjustments to zero, yielding `(n - 1) * u ≤ n * γ` for every `R`-round `Protocol P K R`
  achieving skew `γ`.
* **Matching upper bound (`lundeliusLynchAvg`, `lundeliusLynchAvg_achievesSkew`):** In 1 round,
  each process broadcasts at local clock reading `0` and sets its adjustment to the average of
  `estDiff d_min d_max p arrival q` over all `q : P`. For any `p ≠ q`, the two endpoint terms
  `r = p` and `r = q` contribute error at most `u / 2` each while the remaining `n - 2` terms
  contribute at most `u` each, achieving skew `((n - 1) / n) * u`.
* **Sharp minimax characterization (`exists_achievesSkew_iff`):** Across all round counts `R`, a
  deterministic synchronous full-information protocol `Protocol P K R` achieves skew `γ` if and
  only if `((n - 1) / n) * (d_max - d_min) ≤ γ` (trivial `0 ≤ γ` for `n = 1`;
  [Lundelius and Lynch][LundeliusLynch1984] for `n ≥ 2`); in particular, multi-round communication
  (`R > 1`) cannot improve upon 1-round averaging.

## Main definitions

* `Cslib.Distributed.ClockSync.lundeliusLynchAvg`: 1-round all-to-all midpoint-delay averaging
  protocol.

## Main results

* `Cslib.Distributed.ClockSync.lundeliusLynch_lower_bound`: every `R`-round deterministic protocol
  achieving skew `γ` satisfies `((Fintype.card P - 1 : K) / Fintype.card P) * (d_max - d_min) ≤ γ`.
* `Cslib.Distributed.ClockSync.lundeliusLynchAvg_achievesSkew`: `lundeliusLynchAvg` achieves skew
  `((Fintype.card P - 1 : K) / Fintype.card P) * (d_max - d_min)` in 1 round.
* `Cslib.Distributed.ClockSync.exists_achievesSkew_iff`: sharp characterization of achievable
  clock skew across all round counts `R`.

## References

* [J. Lundelius, N. Lynch, *An upper and lower bound for clock synchronization*][LundeliusLynch1984]
-/

public section

namespace Cslib.Distributed.ClockSync

universe u v

/-! ### Prefix-shifted executions and the `(1 - 1 / n) * (d_max - d_min)` lower bound -/

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

/-- **Lundelius–Lynch tight lower bound** (for `2 ≤ Fintype.card P`,
[Lundelius and Lynch][LundeliusLynch1984]; for `Fintype.card P = 1`, `0 ≤ γ` from `|x - x| = 0`):
any deterministic synchronous full-information `R`-round protocol `π : Protocol P K R` achieving
worst-case skew `γ` on a nonempty finite complete network `P` against transit delays in
`[d_min, d_max]` (`d_min ≤ d_max`) satisfies
`((Fintype.card P - 1 : K) / Fintype.card P) * (d_max - d_min) ≤ γ`. -/
theorem lundeliusLynch_lower_bound {P : Type u} [Fintype P] [Nonempty P]
    {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {R : ℕ} {π : Protocol P K R} {d_min d_max γ : K}
    (hd : d_min ≤ d_max) (hπ : AchievesSkew π d_min d_max γ) :
    ((Fintype.card P - 1 : K) / Fintype.card P) * (d_max - d_min) ≤ γ := by
  set n := Fintype.card P
  have hn_pos : 1 ≤ n := Fintype.card_pos
  have hnK : (0 : K) < n := Nat.cast_pos.mpr hn_pos
  by_cases hn1 : n = 1
  · obtain ⟨p₀⟩ := ‹Nonempty P›
    have hδ : ValidDelays (P := P) d_min d_max (fun _ _ _ => d_min) :=
      fun _ _ _ => ⟨le_rfl, hd⟩
    have h0 : |π.syncOffset (fun _ => 0) (fun _ _ _ => d_min) p₀ -
        π.syncOffset (fun _ => 0) (fun _ _ _ => d_min) p₀| ≤ γ :=
      hπ (fun _ => 0) (fun _ _ _ => d_min) hδ p₀ p₀
    simp only [sub_self, abs_zero] at h0
    rw [hn1]
    simp only [Nat.cast_one, sub_self, zero_div, zero_mul]
    exact h0
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
      rw [syncOffset_shift_eq, syncOffset_shift_eq] at hskew
      have hs0 : s (k + 1) p₀ = u := by
        simp only [s, p₀, Equiv.apply_symm_apply, lt_add_one, ↓reduceIte]
      have hs1 : s (k + 1) p₁ = 0 := by
        simp only [s, p₁, Equiv.apply_symm_apply, lt_self_iff_false, ↓reduceIte]
      rw [hs0, hs1, add_zero] at hskew
      have hle : (π.syncOffset c₀ δ₀ p₀ + u) - π.syncOffset c₀ δ₀ p₁ ≤ γ :=
        (le_abs_self _).trans hskew
      have hz0 : z k = π.syncOffset c₀ δ₀ p₀ := by simp only [z, hk0, ↓reduceDIte, p₀]
      have hz1 : z (k + 1) = π.syncOffset c₀ δ₀ p₁ := by simp only [z, hk1, ↓reduceDIte, p₁]
      linarith
    have hsum := Finset.sum_le_sum hstep
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, nsmul_eq_mul, Finset.sum_range_sub' z (n - 1)] at hsum
    have hbase : z (n - 1) - z 0 ≤ γ := by
      have hδ₀ : ValidDelays d_min d_max δ₀ := by
        intro _ p q
        dsimp only [δ₀]
        split_ifs
        · exact ⟨le_rfl, hd⟩
        · exact ⟨hd, le_rfl⟩
      have hlast_lt : n - 1 < n := by omega
      have hzero_lt : 0 < n := by omega
      have h0 := hπ c₀ δ₀ hδ₀ (e.symm ⟨n - 1, hlast_lt⟩) (e.symm ⟨0, hzero_lt⟩)
      have hle := (le_abs_self _).trans h0
      have hz_last : z (n - 1) = π.syncOffset c₀ δ₀ (e.symm ⟨n - 1, hlast_lt⟩) := by
        simp only [z, hlast_lt, ↓reduceDIte]
      have hz_zero : z 0 = π.syncOffset c₀ δ₀ (e.symm ⟨0, hzero_lt⟩) := by
        simp only [z, hzero_lt, ↓reduceDIte]
      linarith
    have hcast : ((n - 1 : ℕ) : K) = (n : K) - 1 := by
      rw [Nat.cast_sub hn_pos, Nat.cast_one]
    rw [hcast] at hsum
    have htotal : ((n : K) - 1) * u ≤ (n : K) * γ := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hnK]
    linarith

/-! ### Matching 1-round averaging upper bound and minimax characterization -/

/-- The 1-round all-to-all midpoint-delay averaging protocol of
[Lundelius and Lynch][LundeliusLynch1984]: every process broadcasts at local clock reading `0`
and sets its clock adjustment to `(∑ q : P, estDiff d_min d_max p v.lastArrival q) / |P|`. -/
@[expose] def lundeliusLynchAvg {P : Type u} [Fintype P] [DecidableEq P]
    {K : Type v} [Field K] (d_min d_max : K) : Protocol P K 1 where
  sendTime _ _ _ _ := 0
  adjust p v := (∑ q : P, estDiff d_min d_max p v.lastArrival q) / Fintype.card P

/-- **Lundelius–Lynch averaging upper bound** [Lundelius and Lynch][LundeliusLynch1984]: the
1-round averaging protocol `lundeliusLynchAvg` achieves worst-case clock skew
`((Fintype.card P - 1 : K) / Fintype.card P) * (d_max - d_min)` whenever `d_min ≤ d_max`. -/
theorem lundeliusLynchAvg_achievesSkew {P : Type u} [Fintype P] [DecidableEq P] [Nonempty P]
    {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {d_min d_max : K} (hd : d_min ≤ d_max) :
    AchievesSkew (lundeliusLynchAvg (P := P) d_min d_max) d_min d_max
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
    have h1 : (0 : K) ≤ ((n : K) - 1) / n :=
      div_nonneg (by have : (1 : K) ≤ n := Nat.one_le_cast.mpr hn_pos; linarith) hnK_pos.le
    exact mul_nonneg h1 (sub_nonneg.mpr hd)
  · let recv : P → P → K := fun x r => arrivalReading c δ 0 r x 0
    let xEst : P → P → K := fun x r => c x + estDiff d_min d_max x (recv x) r
    have hsync : ∀ x : P,
        (lundeliusLynchAvg d_min d_max).syncOffset c δ x = (∑ r : P, xEst x r) / n := by
      intro x
      have hsum : ∑ r : P, xEst x r = n * c x + ∑ r : P, estDiff d_min d_max x (recv x) r := by
        simp only [xEst, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          n]
      dsimp only [Protocol.syncOffset, Protocol.adj, lundeliusLynchAvg, Protocol.localView,
        LocalView.lastArrival, n]
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
    let rest : Finset P := (Finset.univ.erase p).erase q
    have hrest_term : ∀ r ∈ rest, |xEst p r - xEst q r| ≤ u := by
      intro r _
      have htri : |xEst p r - xEst q r| ≤ |xEst p r - c r| + |xEst q r - c r| := by
        have hsplit : xEst p r - xEst q r = (xEst p r - c r) - (xEst q r - c r) := by ring
        rw [hsplit]
        exact abs_sub _ _
      linarith [herr p r, herr q r]
    have hp_not_rest : p ∉ rest := by
      simp only [rest, Finset.mem_erase, ne_eq, not_true_eq_false, false_and, and_false,
        not_false_eq_true]
    have hq_not_rest : q ∉ rest := Finset.notMem_erase q _
    have huniv : (Finset.univ : Finset P) = insert p (insert q rest) := by
      ext r
      simp only [rest, Finset.mem_univ, Finset.mem_insert, Finset.mem_erase, true_iff]
      tauto
    have hcard_rest : rest.card = n - 2 := by
      have hc1 : (Finset.univ.erase p : Finset P).card = n - 1 :=
        Finset.card_erase_of_mem (Finset.mem_univ p)
      have hq_mem : q ∈ (Finset.univ.erase p : Finset P) :=
        Finset.mem_erase.mpr ⟨Ne.symm hpq, Finset.mem_univ q⟩
      rw [Finset.card_erase_of_mem hq_mem, hc1]
      omega
    have hn2 : 2 ≤ n := by
      have := Finset.card_le_card (show ({p, q} : Finset P) ⊆ Finset.univ from Finset.subset_univ _)
      rwa [Finset.card_pair hpq, Finset.card_univ] at this
    have hsum_bound : ∑ r : P, |xEst p r - xEst q r| ≤ ((n : K) - 1) * u := by
      rw [huniv, Finset.sum_insert (by simp only [Finset.mem_insert, hpq, hp_not_rest, or_self,
        not_false_eq_true]), Finset.sum_insert hq_not_rest]
      have hrest_sum : ∑ r ∈ rest, |xEst p r - xEst q r| ≤ ((n - 2 : ℕ) : K) * u := by
        calc ∑ r ∈ rest, |xEst p r - xEst q r|
            ≤ ∑ _ ∈ rest, u := Finset.sum_le_sum hrest_term
          _ = ((n - 2 : ℕ) : K) * u := by
            rw [Finset.sum_const, hcard_rest, nsmul_eq_mul]
      have hcast2 : ((n - 2 : ℕ) : K) = (n : K) - 2 := by
        rw [Nat.cast_sub hn2, Nat.cast_ofNat]
      rw [hcast2] at hrest_sum
      linarith
    rw [hsync p, hsync q, ← sub_div, abs_div, abs_of_pos hnK_pos, ← Finset.sum_sub_distrib,
      div_mul_eq_mul_div, div_le_div_iff_of_pos_right hnK_pos]
    exact (Finset.abs_sum_le_sum_abs _ _).trans hsum_bound

/-- **Minimax skew characterization for synchronous `R`-round protocols**: there exists a round
count `R` and a deterministic synchronous full-information protocol `π : Protocol P K R` achieving
worst-case clock skew `γ` on `P` against transit delays in `[d_min, d_max]` (`d_min ≤ d_max`) if
and only if `((Fintype.card P - 1 : K) / Fintype.card P) * (d_max - d_min) ≤ γ` (trivial `0 ≤ γ`
for `Fintype.card P = 1`; `lundeliusLynch_lower_bound` and `lundeliusLynchAvg_achievesSkew` after
[Lundelius and Lynch][LundeliusLynch1984] for `2 ≤ Fintype.card P`). -/
theorem exists_achievesSkew_iff {P : Type u} [Fintype P] [Nonempty P]
    {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {d_min d_max γ : K} (hd : d_min ≤ d_max) :
    (∃ (R : ℕ) (π : Protocol P K R), AchievesSkew π d_min d_max γ) ↔
      ((Fintype.card P - 1 : K) / Fintype.card P) * (d_max - d_min) ≤ γ := by
  constructor
  · rintro ⟨R, π, hπ⟩
    exact lundeliusLynch_lower_bound hd hπ
  · intro hγ
    let _ := Classical.decEq P
    exact ⟨1, lundeliusLynchAvg d_min d_max, (lundeliusLynchAvg_achievesSkew hd).mono hγ⟩

end Cslib.Distributed.ClockSync
