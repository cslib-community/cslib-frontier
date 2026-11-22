/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.Interfaces
public import CslibFrontier.Computability.Complexity.Classes.Time.AcceptCount
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ExactTerm
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.SqrtLogGrowth
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.ProgClock

/-!
# The doubling clocks for a general halting test and decision

`decidable_of_clockedTests` is the clock search of Theorem 2.4 (its proof in §2), stated for an
arbitrary halting test `Hq` and decision `Dq`, both programs over `[τ, n]`. The decider tries the
clocks `τ = (n + K₀) · 2^j` and decides with `Dq` at the first clock at which `Hq` is positive. If
`Hq` is positive at every clock beyond `c₁ t(n) + c₂`, and `Dq` decides the problem at every clock
at which `Hq` is positive, with values below `2^(C·SqrtLog τ)`, the problem is decided in time
`2^(C·SqrtLog t(n))` and space `C·SqrtLog t(n)`. The argument is the one of
`Cross.GeneralTheorem.generalSimulation_of_clocked`, which is the case of the accept count of a
nondeterministic machine.
-/

public section

namespace Cslib.Complexity.NtimeDspace.Cross

open NtimeDspace.ProgLang _root_.Turing _root_.Turing.MultiTapeTM

/-- **The doubling clocks, for a general test.** -/
theorem decidable_of_clockedTests {t : ℕ → ℕ} (ht : ∀ n, n ≤ t n) (A : Set (List Bool))
    (Hq Dq : Prog) (CH CD τH c₁ c₂ : ℕ)
    (hHb : ∀ (a : List Bool) τ, a.length ≤ τ → τH ≤ τ →
      Hq.Bounded a (2 ^ (CH * SqrtLog τ)) [τ, a.length])
    (hHpos : ∀ (a : List Bool) τ, a.length ≤ τ → τH ≤ τ → c₁ * t a.length + c₂ ≤ τ →
      0 < Hq.eval a [τ, a.length])
    (hD : ∀ (a : List Bool) τ, a.length ≤ τ → τH ≤ τ → 0 < Hq.eval a [τ, a.length] →
      Dq.Bounded a (2 ^ (CD * SqrtLog τ)) [τ, a.length] ∧
        (0 < Dq.eval a [τ, a.length] ↔ a ∈ A)) :
    ∃ C, DecidableInTimeAndSpace A encBits (fun a => 2 ^ (C * SqrtLog (t a.length)))
      (fun a => C * SqrtLog (t a.length)) := by
  classical
  obtain ⟨K₀, hK₀⟩ : ∃ K₀, K₀ = τH + 1 := ⟨_, rfl⟩
  let T0 : Prog := .add (.var 0) (.const K₀)
  have hclock (a : List Bool) (j : ℕ) : clockAt T0 a j = (a.length + K₀) * 2 ^ j := by
    simp [clockAt, T0, Prog.eval]
  obtain ⟨α₁, hα₁⟩ : ∃ α₁, α₁ = 2 * c₁ + 1 := ⟨_, rfl⟩
  obtain ⟨β₁, hβ₁⟩ : ∃ β₁, β₁ = 2 * c₂ + K₀ := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = 2 * (α₁ + β₁ + 1) := ⟨_, rfl⟩
  obtain ⟨Kc, hKc⟩ : ∃ Kc, Kc = (CH + CD + 1) * G + (α₁ + β₁ + 1) + (1 + K₀ + 1) := ⟨_, rfl⟩
  have hαt (m : ℕ) : α₁ * m = 2 * (c₁ * m) + m := by rw [hα₁]; ring
  have hS (a : List Bool) : 1 ≤ SqrtLog (t a.length) := Nat.le_add_left _ _
  have hlt (a : List Bool) : t a.length < 2 ^ SqrtLog (t a.length) := lt_two_pow_sqrtLog _
  have hclock_ge (a : List Bool) (j : ℕ) : a.length + K₀ ≤ clockAt T0 a j := by
    rw [hclock]; exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos j)
  have hvalid (a : List Bool) (j : ℕ) : a.length ≤ clockAt T0 a j ∧ τH ≤ clockAt T0 a j := by
    have := hclock_ge a j; omega
  have hbefore (a : List Bool) (j : ℕ)
      (hrun : ∀ i < j, Hq.eval a [clockAt T0 a i, a.length] = 0) :
      clockAt T0 a j ≤ α₁ * t a.length + β₁ := by
    have hn := ht a.length
    rcases j with _ | i
    · rw [hclock]; simp only [pow_zero, mul_one]; have := hαt (t a.length); omega
    · have h0 := hrun i (Nat.lt_succ_self i)
      have hlt' : clockAt T0 a i < c₁ * t a.length + c₂ := by
        by_contra hge
        have := hHpos a _ (hvalid a i).1 (hvalid a i).2 (Nat.le_of_not_lt hge)
        omega
      rw [clockAt_succ]
      have := hαt (t a.length)
      omega
  have hpow (a : List Bool) (C : ℕ) (j : ℕ) (hj : clockAt T0 a j ≤ α₁ * t a.length + β₁)
      (hCle : C ≤ CH + CD + 1) :
      2 ^ (C * SqrtLog (clockAt T0 a j)) ≤ 2 ^ (Kc * SqrtLog (t a.length)) := by
    refine Nat.pow_le_pow_right (by norm_num) ?_
    calc C * SqrtLog (clockAt T0 a j) ≤ (CH + CD + 1) * (G * SqrtLog (t a.length)) :=
          Nat.mul_le_mul hCle (hG ▸ sqrtLog_le_of_le_mul_add α₁ β₁ (by omega) hj)
      _ ≤ Kc * SqrtLog (t a.length) := by
          rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
  refine decidable_of_prog_clock_first A T0 Hq Dq (fun a => SqrtLog (t a.length))
    (fun a => Kc * SqrtLog (t a.length)) Kc ?_ ?_ (fun _ => le_rfl) ?_ ?_ ?_ ?_ ?_
  all_goals try simp only [encBits_apply]
  · intro a
    exact (Nat.add_le_add_right (log2_mono (ht a.length)) 1).trans (log2_add_one_le_sqrtLog _)
  · intro a
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by have := hS a; omega))
  · intro a
    refine (ht a.length).trans ((hlt a).le.trans (Nat.pow_le_pow_right (by norm_num) ?_))
    exact Nat.le_mul_of_pos_left _ (by omega)
  · intro a
    have h1 : 1 * t a.length + K₀ ≤ 2 ^ ((1 + K₀ + 1) * SqrtLog (t a.length)) :=
      mul_add_le_two_pow 1 K₀ (hlt a) (hS a)
    have h2 : (1 + K₀ + 1) * SqrtLog (t a.length) ≤ Kc * SqrtLog (t a.length) :=
      Nat.mul_le_mul_right _ (by omega)
    have hn := ht a.length
    simp only [T0, Prog.Bounded, Prog.eval, List.getD_cons_zero]
    refine ⟨trivial, ?_, ?_⟩
    · exact (by omega : K₀ ≤ 1 * t a.length + K₀).trans
        (h1.trans (Nat.pow_le_pow_right (by norm_num) h2))
    · exact (by omega : a.length + K₀ ≤ 1 * t a.length + K₀).trans
        (h1.trans (Nat.pow_le_pow_right (by norm_num) h2))
  · intro a
    refine ⟨c₁ * t a.length + c₂, ?_⟩
    have hge : c₁ * t a.length + c₂ ≤ clockAt T0 a (c₁ * t a.length + c₂) := by
      rw [hclock]
      have := Nat.lt_two_pow_self (n := c₁ * t a.length + c₂)
      have : 2 ^ (c₁ * t a.length + c₂) ≤ (a.length + K₀) * 2 ^ (c₁ * t a.length + c₂) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    exact hHpos a _ (hvalid a _).1 (hvalid a _).2 hge
  · intro a j hrun
    have hj := hbefore a j hrun
    refine ⟨bounded_mono_pow (hpow a CH j hj (by omega)) (hHb a _ (hvalid a j).1 (hvalid a j).2),
      ?_⟩
    refine hj.trans ((mul_add_le_two_pow α₁ β₁ (hlt a) (hS a)).trans
      (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ ?_)))
    omega
  · intro a j hrun hpos
    have hj := hbefore a j hrun
    obtain ⟨hb, hdec⟩ := hD a _ (hvalid a j).1 (hvalid a j).2 hpos
    refine ⟨bounded_mono_pow (hpow a CD j hj (by omega)) hb, ?_⟩
    rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero]
    exact hdec
where
  /-- Value bounds are monotone in the bound. -/
  bounded_mono_pow {w : List Bool} {B B' : ℕ} (hB : B ≤ B') {P : Prog} {env : List ℕ}
      (h : P.Bounded w B env) : P.Bounded w B' env :=
    Exact.bounded_mono hB P env h

end Cslib.Complexity.NtimeDspace.Cross
