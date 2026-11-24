/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ScaleInterface
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.HaltCount
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.ProgClock

/-!
# Theorem 2.4 for every time bound (the doubling clocks)

`generalSimulation_of_clocked` derives Theorem 1.1 for every `t(n) ≥ n`, not necessarily
constructible, from the clocked counter `ClockedCounting`. This is the proof of Theorem 2.4
(§2 of the paper), for a scale `D` with the regularity `Scale D` (`D = SqrtLog` for Theorem 1.1;
the scale also allows other bounds, such as `D = RootLog 3`):

* By `HaltCount.exists_haltCount_of_mem_NTIME`, a problem in `NTIME[t]` has a closed fair-coin
  table `M` and its halt marker `Mh`. The marker accepts all `2 ^ τ` coin strings exactly when
  every replay of `M` on `τ` coins has halted; this holds once `τ ≥ c₁ t(n) + c₂`; and then
  membership is a positive accepting count of `M`.
* `ClockedCounting` for `Mh` with `b = 1` is the halting test, and for `M` with `b = 0` the
  decision, both at the coin length `paddedTime τ ≥ τ` of the clock `τ`.
* The decider tries the clocks `τ = (n + K₀) · 2 ^ j` (`ProgLang.decidable_of_prog_clock_first`)
  and stops at the first clock at which every replay has halted. Before it stops, some replay
  still runs at the previous clock, so every clock it tries is at most
  `(2c₁ + 1) t(n) + 2c₂ + K₀`; `D` changes by a constant factor on them
  (`Scale.linear`).

The paper's version detects halting by counting the computations still running; here the count is
that of the halt marker, which is the same test. The constant `K₀` lifts the first clock above the
thresholds of the two clocked counters.

## Main results

* `Cslib.Complexity.NtimeDspace.Cross.generalSimulationAt_of_clocked`: `ClockedCountingAt D →
GeneralSimulationAt D`
  for every scale `D` (`Scale D`).
* `Cslib.Complexity.NtimeDspace.Cross.generalSimulation_of_clocked`: `ClockedCounting →
GeneralSimulation`, the case
  `D = SqrtLog`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross

open NtimeDspace.ProgLang NtimeDspace.SumProduct Cslib.Complexity
    Cslib.Complexity.CountingSimulation
  _root_.Turing _root_.Turing.MultiTapeTM

variable {w : List Bool}

/-! ### Programs over `[τ, n]` from programs over `[τ, n, b]` -/

/-- Value bounds are monotone in the bound. -/
private theorem bounded_mono {B B' : ℕ} (hB : B ≤ B') :
    ∀ (P : Prog) (env : List ℕ), P.Bounded w B env → P.Bounded w B' env
  | .const _, _, h => le_trans h hB
  | .var _, _, _ => trivial
  | .add a b, env, ⟨ha, hb, h⟩ =>
    ⟨bounded_mono hB a env ha, bounded_mono hB b env hb, le_trans h hB⟩
  | .sub a b, env, ⟨ha, hb⟩ => ⟨bounded_mono hB a env ha, bounded_mono hB b env hb⟩
  | .mul a b, env, ⟨ha, hb, h⟩ =>
    ⟨bounded_mono hB a env ha, bounded_mono hB b env hb, le_trans h hB⟩
  | .div a b, env, ⟨ha, hb⟩ => ⟨bounded_mono hB a env ha, bounded_mono hB b env hb⟩
  | .mod a b, env, ⟨ha, hb⟩ => ⟨bounded_mono hB a env ha, bounded_mono hB b env hb⟩
  | .bit a i, env, ⟨ha, hi⟩ => ⟨bounded_mono hB a env ha, bounded_mono hB i env hi⟩
  | .lt a b, env, ⟨ha, hb⟩ => ⟨bounded_mono hB a env ha, bounded_mono hB b env hb⟩
  | .input a, env, ha => bounded_mono hB a env ha
  | .ite c t e, env, ⟨hc, h⟩ => by
    refine ⟨bounded_mono hB c env hc, ?_⟩
    split_ifs at h ⊢
    · exact bounded_mono hB t env h
    · exact bounded_mono hB e env h
  | .letIn a body, env, ⟨ha, hbody⟩ => ⟨bounded_mono hB a env ha, bounded_mono hB body _ hbody⟩
  | .fold n init body, env, ⟨hn, hi, hle, hk⟩ =>
    ⟨bounded_mono hB n env hn, bounded_mono hB init env hi, le_trans hle hB,
      fun k hk' => bounded_mono hB body _ (hk k hk')⟩

/-- Run a program over `[τ, n, b]` on the environment `[τ, n]`, with `b` fixed. -/
def withBit (q : Prog) (b : ℕ) : Prog := .letIn (.const b) (.letIn (.var 2) (.letIn (.var 2) q))

theorem eval_withBit {q : Prog} (hq : Prog'.closed 3 q = true) (b τ n : ℕ) :
    (withBit q b).eval w [τ, n] = q.eval w [τ, n, b] := by
  have := Prog'.eval_append (w := w) q [τ, n, b] [τ, n] (by simpa using hq)
  simpa [withBit, Prog.eval] using this

theorem bounded_withBit {q : Prog} (hq : Prog'.closed 3 q = true) {B b τ n : ℕ} (hb : b ≤ B)
    (h : q.Bounded w B [τ, n, b]) : (withBit q b).Bounded w B [τ, n] := by
  have := (Prog'.bounded_append (w := w) B q [τ, n, b] [τ, n] (by simpa using hq)).mpr h
  simp only [withBit, Prog.Bounded, Prog.eval]
  exact ⟨hb, trivial, trivial, by simpa using this⟩

/-- The halting test: `1` when the clocked counter reports a count equal to `2 ^ paddedTime τ`. -/
def haltTest (QH : Prog) : Prog := .lt (withBit QH 1) (.const 1)

theorem eval_haltTest {QH : Prog} (hq : Prog'.closed 3 QH = true) (τ n : ℕ) :
    (haltTest QH).eval w [τ, n] = if QH.eval w [τ, n, 1] = 0 then 1 else 0 := by
  simp only [haltTest, Prog.eval, eval_withBit hq]
  split_ifs <;> omega

/-- The first clock `n + K₀`. -/
def firstClock (K₀ : ℕ) : Prog := .add (.var 0) (.const K₀)

theorem clockAt_firstClock (K₀ : ℕ) (w : List Bool) (j : ℕ) :
    clockAt (firstClock K₀) w j = (w.length + K₀) * 2 ^ j := by
  simp [clockAt, firstClock, Prog.eval]

/-! ### The transfer theorem -/

/-- **Theorem 2.4 at a scale `D`, for every time bound `t(n) ≥ n`.** The clocked counter at the
scale `D` gives Theorem 1.1 for every `t(n) ≥ n`, constructible or not: every problem in `NTIME[t]`
is decided in simultaneous deterministic time `2^(C·D (t n))` and space `C·D (t n)`. -/
theorem generalSimulationAt_of_clocked {D : ℕ → ℕ} (hD : Scale D) (hC : ClockedCountingAt D) :
    GeneralSimulationAt D := by
  intro t ht A hA
  classical
  obtain ⟨k, State, hfin, M, Mh, c₁, c₂, -, hhalt, hmem, -⟩ :=
    HaltCount.exists_haltCount_of_mem_NTIME hA
  obtain ⟨QM, CM, τM, hQMc, hQM⟩ := hC k State M
  obtain ⟨QH, CH, τH, hQHc, hQH⟩ := hC k State Mh
  simp only [encBits_apply] at hhalt hmem
  -- the clocks
  obtain ⟨K₀, hK₀⟩ : ∃ K₀, K₀ = τM + τH + 1 := ⟨_, rfl⟩
  set T0 := firstClock K₀
  set H := haltTest QH
  set P := withBit QM 0
  -- the clocks tried stay below `α₁ · t n + β₁`
  obtain ⟨α₁, hα₁⟩ : ∃ α₁, α₁ = 2 * c₁ + 1 := ⟨_, rfl⟩
  obtain ⟨β₁, hβ₁⟩ : ∃ β₁, β₁ = 2 * c₂ + K₀ := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = 2 * (α₁ + β₁ + 1) := ⟨_, rfl⟩
  obtain ⟨Kc, hKc⟩ : ∃ Kc, Kc = (CM + CH + 1) * G + (α₁ + β₁ + 1) + (1 + K₀ + 1) := ⟨_, rfl⟩
  have hαt (m : ℕ) : α₁ * m = 2 * (c₁ * m) + m := by rw [hα₁]; ring
  -- facts about one input
  have hS (a : List Bool) : 1 ≤ D (t a.length) := hD.one_le _
  have hlt (a : List Bool) : t a.length < 2 ^ D (t a.length) := hD.lt_two_pow _
  have hclock (a : List Bool) (j : ℕ) : clockAt T0 a j = (a.length + K₀) * 2 ^ j :=
    clockAt_firstClock K₀ a j
  have hclock_ge (a : List Bool) (j : ℕ) : a.length + K₀ ≤ clockAt T0 a j := by
    rw [hclock]; exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos j)
  -- the counters at a clock
  have hvalid (a : List Bool) (j : ℕ) :
      a.length ≤ clockAt T0 a j ∧ τM ≤ clockAt T0 a j ∧ τH ≤ clockAt T0 a j := by
    have := hclock_ge a j; omega
  have hHeval (a : List Bool) (j : ℕ) :
      H.eval a [clockAt T0 a j, a.length] = 0 ↔
        Mh.acceptCount a (paddedTime (clockAt T0 a j)) ≠ 1 * 2 ^ paddedTime (clockAt T0 a j) := by
    obtain ⟨h1, -, h3⟩ := hvalid a j
    rw [eval_haltTest hQHc, ← (hQH a _ 1 h1 h3 le_rfl).1]
    rcases Nat.eq_zero_or_pos (QH.eval a [clockAt T0 a j, a.length, 1]) with h0 | h0
    · simp [h0]
    · simp [Nat.pos_iff_ne_zero.mp h0, h0]
  -- the clocks tried before stopping
  have hbefore (a : List Bool) (j : ℕ)
      (hrun : ∀ i < j, H.eval a [clockAt T0 a i, a.length] = 0) :
      clockAt T0 a j ≤ α₁ * t a.length + β₁ := by
    have hn := ht a.length
    rcases j with _ | i
    · rw [hclock]; simp only [pow_zero, mul_one]; have := hαt (t a.length); omega
    · have h0 := (hHeval a i).mp (hrun i (Nat.lt_succ_self i))
      have hlt' : clockAt T0 a i < c₁ * t a.length + c₂ := by
        by_contra hge
        exact h0 (by
          rw [one_mul]
          exact hhalt a _ ((Nat.le_of_not_lt hge).trans (le_paddedTime _)))
      rw [clockAt_succ]
      have := hαt (t a.length)
      omega
  have hSqrt (a : List Bool) (j : ℕ) (hj : clockAt T0 a j ≤ α₁ * t a.length + β₁) :
      D (clockAt T0 a j) ≤ G * D (t a.length) :=
    hG ▸ hD.linear α₁ β₁ (by omega) hj
  have hpow (a : List Bool) (C : ℕ) (j : ℕ) (hj : clockAt T0 a j ≤ α₁ * t a.length + β₁)
      (hCle : C ≤ CM + CH + 1) :
      2 ^ (C * D (clockAt T0 a j)) ≤ 2 ^ (Kc * D (t a.length)) := by
    refine Nat.pow_le_pow_right (by norm_num) ?_
    calc C * D (clockAt T0 a j) ≤ (CM + CH + 1) * (G * D (t a.length)) :=
          Nat.mul_le_mul hCle (hSqrt a j hj)
      _ ≤ Kc * D (t a.length) := by
          rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
  refine decidable_of_prog_clock_first A T0 H P (fun a => D (t a.length))
    (fun a => Kc * D (t a.length)) Kc ?_ ?_ (fun _ => le_rfl) ?_ ?_ ?_ ?_ ?_
  all_goals try simp only [encBits_apply]
  · -- logarithmic budget
    intro a
    exact (Nat.add_le_add_right (log2_mono (ht a.length)) 1).trans (hD.log_le _)
  · -- `1 ≤ K`
    intro a
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by have := hS a; omega))
  · -- the input length
    intro a
    refine (ht a.length).trans ((hlt a).le.trans (Nat.pow_le_pow_right (by norm_num) ?_))
    exact Nat.le_mul_of_pos_left _ (by omega)
  · -- the first clock
    intro a
    have h1 : 1 * t a.length + K₀ ≤ 2 ^ ((1 + K₀ + 1) * D (t a.length)) :=
      mul_add_le_two_pow 1 K₀ (hlt a) (hS a)
    have h2 : (1 + K₀ + 1) * D (t a.length) ≤ Kc * D (t a.length) :=
      Nat.mul_le_mul_right _ (by omega)
    have hn := ht a.length
    simp only [T0, firstClock, Prog.Bounded, Prog.eval, List.getD_cons_zero]
    refine ⟨trivial, ?_, ?_⟩
    · exact (by omega : K₀ ≤ 1 * t a.length + K₀).trans
        (h1.trans (Nat.pow_le_pow_right (by norm_num) h2))
    · exact (by omega : a.length + K₀ ≤ 1 * t a.length + K₀).trans
        (h1.trans (Nat.pow_le_pow_right (by norm_num) h2))
  · -- the search stops
    intro a
    refine ⟨c₁ * t a.length + c₂, ?_⟩
    have hge : c₁ * t a.length + c₂ ≤ clockAt T0 a (c₁ * t a.length + c₂) := by
      rw [hclock]
      have := Nat.lt_two_pow_self (n := c₁ * t a.length + c₂)
      have : 2 ^ (c₁ * t a.length + c₂) ≤ (a.length + K₀) * 2 ^ (c₁ * t a.length + c₂) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hall := hhalt a _ (hge.trans (le_paddedTime _))
    have : H.eval a [clockAt T0 a (c₁ * t a.length + c₂), a.length] ≠ 0 := fun h0 =>
      (hHeval a _).mp h0 (by rw [one_mul]; exact hall)
    omega
  · -- bounds at the clocks tried
    intro a j hrun
    have hj := hbefore a j hrun
    obtain ⟨h1, -, h3⟩ := hvalid a j
    refine ⟨?_, ?_⟩
    · have hb := (hQH a _ 1 h1 h3 le_rfl).2
      have hB : 2 ^ (CH * D (clockAt T0 a j)) ≤ 2 ^ (Kc * D (t a.length)) :=
        hpow a CH j hj (by omega)
      refine ⟨bounded_withBit hQHc Nat.one_le_two_pow (bounded_mono hB _ _ hb),
        Nat.one_le_two_pow⟩
    · refine hj.trans ((mul_add_le_two_pow α₁ β₁ (hlt a) (hS a)).trans
        (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ ?_)))
      omega
  · -- the decision at the stopping clock
    intro a j hrun hpos
    have hj := hbefore a j hrun
    obtain ⟨h1, h2, -⟩ := hvalid a j
    have hb := (hQM a _ 0 h1 h2 (Nat.zero_le _)).2
    have hB : 2 ^ (CM * D (clockAt T0 a j)) ≤ 2 ^ (Kc * D (t a.length)) :=
      hpow a CM j hj (by omega)
    refine ⟨bounded_withBit hQMc (Nat.zero_le _) (bounded_mono hB _ _ hb), ?_⟩
    have hall : Mh.acceptCount a (paddedTime (clockAt T0 a j)) =
        2 ^ paddedTime (clockAt T0 a j) := by
      by_contra hne
      have := (hHeval a j).mpr (by rw [one_mul]; exact hne)
      omega
    rw [hmem a _ hall, eval_withBit hQMc, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero,
      (hQM a _ 0 h1 h2 (Nat.zero_le _)).1, zero_mul, Nat.pos_iff_ne_zero]

/-- **Theorem 2.4 with `D = SqrtLog`, for every time bound `t(n) ≥ n`.** The clocked counter
gives Theorem 1.1 for every `t(n) ≥ n`, constructible or not: every problem in `NTIME[t]` is
decided in simultaneous deterministic time `2^(C·SqrtLog (t n))` and space `C·SqrtLog (t n)`. -/
theorem generalSimulation_of_clocked (hC : ClockedCounting) : GeneralSimulation :=
  generalSimulationAt_of_clocked scale_sqrtLog hC

end Cslib.Complexity.NtimeDspace.Cross
