/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ColumnAdderAt
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.Corollaries
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.CountingPP
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.GeneralTheorem

/-!
# Theorem 2.3 at a scale `D` gives `NTIME[t]`, `PPTIME[t]` and `BPTIME[t]` in space `O(D(t))`

The paper (§8) observes that its method "cannot tell nondeterminism from counting": computing the
counts of the block networks (Theorem 2.3) in a smaller space `D` would improve the simulation of
`PPTIME[t]` exactly as it improves Theorem 1.1. This module proves that remark in the form the
formalization gives it. Let `D` be a scale (`Scale D`: `log₂ n + 1 ≤ D n`, linear changes of the
argument change `D` by a constant factor, `D` sublinear) whose values fit the carry of the column
adder over schedules (`CarryFits D`: `numBlocks n = O(D n)`, i.e. `D(n) = Ω(n / log n)`). If the
bits of the block networks are computed in values below `2 ^ (C · D τ)` (`BlockBitsAt D`), then for
every `t(n) ≥ n`:

* every problem in `NTIME[t]` is decided in simultaneous time `2 ^ (C · D (t n))` and space
  `C · D (t n)` (`generalSimulationAt_of_blockBitsAt`), so `NTIME[t] ⊆ DSPACE[D ∘ t]`
  (`ntime_subset_dspace_of_blockBitsAt`);
* every problem in `PPTIME[t]` likewise (`pptime_decidedAt_of_blockBitsAt`), so
  `PPTIME[t] ⊆ DSPACE[D ∘ t]` (`pptime_subset_dspace_of_blockBitsAt`), and hence
  `BPTIME[t] ⊆ DSPACE[D ∘ t]` (`bptime_subset_dspace_of_blockBitsAt`).

The same block bits feed both: `clockedBitsAt_of_blockBitsAt` (the column adder) gives the clocked
bits, from which the count test and the transfer theorem with doubling clocks
(`generalSimulationAt_of_clocked`) give the `NTIME` simulation, and the majority test with the same
doubling clocks (`decidable_of_clockedTestsAt`, `pptime_decidedAt`) gives the `PPTIME` one. The
`PPTIME` argument is that of `CountingPP.lean` with `D` in place of `SqrtLog`.

`CountingAtInstances.lean` checks the hypotheses at `D = SqrtLog` (recovering Theorem 7.1) and at
`D(n) = n / (log₂ n + 1) + log₂ n + 1`, the target scale `t / log t` of the remark.

## Main definitions

* `Cslib.Complexity.NtimeDspace.Cross.DecidedAt D t A`: decided in time `2 ^ (C · D (t n))` and
space `C · D (t n)`.

## Main results

* `Cslib.Complexity.NtimeDspace.Cross.decidable_of_clockedTestsAt`: the doubling clocks for a
general test at a
  scale `D`.
* `Cslib.Complexity.NtimeDspace.Cross.pptime_decidedAt`: `ClockedBitsAt D → PPTIME[t]` decided at
the scale `D`.
* `Cslib.Complexity.NtimeDspace.Cross.generalSimulationAt_of_blockBitsAt`,
  `Cslib.Complexity.NtimeDspace.Cross.ntime_subset_dspace_of_blockBitsAt`,
  `Cslib.Complexity.NtimeDspace.Cross.pptime_subset_dspace_of_blockBitsAt`,
  `Cslib.Complexity.NtimeDspace.Cross.bptime_subset_dspace_of_blockBitsAt`: the endpoints from
  `BlockBitsAt D`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross

open NtimeDspace.ProgLang Exact Cslib Cslib.Complexity Cslib.Complexity.CountingSimulation
  _root_.Turing _root_.Turing.MultiTapeTM

/-! ### The doubling clocks for a general test at a scale `D` -/

/-- **The doubling clocks, for a general test, at a scale `D`.** The decider tries the clocks
`τ = (n + K₀) · 2 ^ j` and decides with `Dq` at the first clock at which `Hq` is positive. This is
`decidable_of_clockedTests` with `D` in place of `SqrtLog`. -/
theorem decidable_of_clockedTestsAt {D : ℕ → ℕ} (hDs : Scale D) {t : ℕ → ℕ} (ht : ∀ n, n ≤ t n)
    (A : Set (List Bool)) (Hq Dq : Prog) (CH CD τH c₁ c₂ : ℕ)
    (hHb : ∀ (a : List Bool) τ, a.length ≤ τ → τH ≤ τ →
      Hq.Bounded a (2 ^ (CH * D τ)) [τ, a.length])
    (hHpos : ∀ (a : List Bool) τ, a.length ≤ τ → τH ≤ τ → c₁ * t a.length + c₂ ≤ τ →
      0 < Hq.eval a [τ, a.length])
    (hD : ∀ (a : List Bool) τ, a.length ≤ τ → τH ≤ τ → 0 < Hq.eval a [τ, a.length] →
      Dq.Bounded a (2 ^ (CD * D τ)) [τ, a.length] ∧
        (0 < Dq.eval a [τ, a.length] ↔ a ∈ A)) :
    ∃ C, DecidableInTimeAndSpace A encBits (fun a => 2 ^ (C * D (t a.length)))
      (fun a => C * D (t a.length)) := by
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
  have hS (a : List Bool) : 1 ≤ D (t a.length) := hDs.one_le _
  have hlt (a : List Bool) : t a.length < 2 ^ D (t a.length) := hDs.lt_two_pow _
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
      2 ^ (C * D (clockAt T0 a j)) ≤ 2 ^ (Kc * D (t a.length)) := by
    refine Nat.pow_le_pow_right (by norm_num) ?_
    calc C * D (clockAt T0 a j) ≤ (CH + CD + 1) * (G * D (t a.length)) :=
          Nat.mul_le_mul hCle (hG ▸ hDs.linear α₁ β₁ (by omega) hj)
      _ ≤ Kc * D (t a.length) := by
          rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
  refine decidable_of_prog_clock_first A T0 Hq Dq (fun a => D (t a.length))
    (fun a => Kc * D (t a.length)) Kc ?_ ?_ (fun _ => le_rfl) ?_ ?_ ?_ ?_ ?_
  all_goals try simp only [encBits_apply]
  · intro a
    exact (Nat.add_le_add_right (log2_mono (ht a.length)) 1).trans (hDs.log_le _)
  · intro a
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by have := hS a; omega))
  · intro a
    refine (ht a.length).trans ((hlt a).le.trans (Nat.pow_le_pow_right (by norm_num) ?_))
    exact Nat.le_mul_of_pos_left _ (by omega)
  · intro a
    have h1 : 1 * t a.length + K₀ ≤ 2 ^ ((1 + K₀ + 1) * D (t a.length)) :=
      mul_add_le_two_pow 1 K₀ (hlt a) (hS a)
    have h2 : (1 + K₀ + 1) * D (t a.length) ≤ Kc * D (t a.length) :=
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
    refine ⟨Exact.bounded_mono (hpow a CH j hj (by omega)) _ _
      (hHb a _ (hvalid a j).1 (hvalid a j).2), ?_⟩
    refine hj.trans ((mul_add_le_two_pow α₁ β₁ (hlt a) (hS a)).trans
      (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ ?_)))
    omega
  · intro a j hrun hpos
    have hj := hbefore a j hrun
    obtain ⟨hb, hdec⟩ := hD a _ (hvalid a j).1 (hvalid a j).2 hpos
    refine ⟨Exact.bounded_mono (hpow a CD j hj (by omega)) _ _ hb, ?_⟩
    rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero]
    exact hdec

/-! ### `PPTIME` at a scale `D` -/

/-- Decided in simultaneous time `2 ^ (C · D (t n))` and space `C · D (t n)`. -/
def DecidedAt (D t : ℕ → ℕ) (A : Set (List Bool)) : Prop :=
  ∃ C, DecidableInTimeAndSpace A encBits (fun a => 2 ^ (C * D (t a.length)))
    (fun a => C * D (t a.length))

theorem decidedAt_sqrtLog {t : ℕ → ℕ} {A : Set (List Bool)} :
    DecidedAt SqrtLog t A ↔ DecidedInSqrtLog t A := Iff.rfl

theorem DecidedAt.mem_DSPACE {D t : ℕ → ℕ} {A : Set (List Bool)} (h : DecidedAt D t A) :
    A ∈ DSPACE encBits (fun n => D (t n)) := by
  obtain ⟨C, hC⟩ := h
  exact mem_DSPACE_iff.mpr ⟨C, 0, _, hC⟩

/-- The bits program of a table at a valid clock, at a scale `D`. -/
theorem bitsOK_ofAt {D : ℕ → ℕ} {k : ℕ} {State : Type} {M : MultiTapePTM k Bool State} {P : Prog}
    {C τ₀ : ℕ}
    (hP : ∀ (w : List Bool) (τ j : ℕ), w.length ≤ τ → τ₀ ≤ τ →
      P.eval w [τ, w.length, j] = M.acceptCount w (paddedTime τ) / 2 ^ j % 2 ∧
        P.Bounded w (2 ^ (C * D τ)) [τ, w.length, j])
    {w : List Bool} {τ : ℕ} (hw : w.length ≤ τ) (hτ : τ₀ ≤ τ) {E : ℕ} (hE : C ≤ E) :
    BitsOK w P τ w.length (M.acceptCount w (paddedTime τ)) (2 ^ (E * D τ)) := fun j =>
  ⟨(hP w τ j hw hτ).1, bounded_mono (Nat.pow_le_pow_right (by norm_num)
    (Nat.mul_le_mul_right _ hE)) _ _ (hP w τ j hw hτ).2⟩

/-- **Theorem 7.1 for `PPTIME` at a scale `D`**, from the clocked bits at the scale `D`: for every
`t(n) ≥ n`, a problem decided by strict majority within `O(t)` is decided in simultaneous time
`2 ^ (C · D (t n))` and space `C · D (t n)`. -/
theorem pptime_decidedAt {D : ℕ → ℕ} (hDs : Scale D) (hB : ClockedBitsAt D) {t : ℕ → ℕ}
    (ht : ∀ n, n ≤ t n) {A : Set (List Bool)} (hA : A ∈ PPTIME encBits t) : DecidedAt D t A := by
  classical
  obtain ⟨c₁, c₂, k, State, hfin, M, hM⟩ := hA
  obtain ⟨PM, CM, τM, hPMc, hPM⟩ := hB k State M
  obtain ⟨PH, CH, τH, hPHc, hPH⟩ := hB k State (HaltCount.haltMark M)
  have hmem := fun a => (hM a)
  simp only [encBits_apply] at hmem
  refine decidable_of_clockedTestsAt hDs ht A (bitAtPad PH) (majorityProg PM) (CH + 2) (CM + 2)
    (max (max τM τH) 2) c₁ c₂ ?_ ?_ ?_
  · intro a τ ha hτ
    exact bounded_bitAtPad hPHc (bitsOK_ofAt hPH ha (by omega) (by omega)) (by omega)
      (lin_le_two_pow_at hDs.log_le τ (by omega))
  · intro a τ ha hτ hT
    rw [eval_bitAtPad hPHc (bitsOK_ofAt hPH ha (by omega) (E := CH + 2) (by omega))]
    refine (eq_two_pow_iff_bit acceptCount_le_two_pow).mp ?_
    rw [HaltCount.acceptCount_haltMark_eq_two_pow_iff]
    exact halted_mono M a (hT.trans (le_paddedTime τ))
      ((halted_support_iff M a _).mp (hmem a).1)
  · intro a τ ha hτ hpos
    have hhalt : ∀ coins : List Bool, coins.length = paddedTime τ →
        (M.stepCoins coins (Cfg.init M.initial a)).state = none := by
      rw [eval_bitAtPad hPHc (bitsOK_ofAt hPH ha (by omega) (E := CH + 2) (by omega)),
        ← eq_two_pow_iff_bit acceptCount_le_two_pow,
        HaltCount.acceptCount_haltMark_eq_two_pow_iff] at hpos
      exact hpos
    have hok := bitsOK_ofAt hPM ha (by omega) (E := CM + 2) (by omega)
    refine ⟨bounded_majorityProg hPMc hok (by omega) (lin_le_two_pow_at hDs.log_le τ (by omega)),
      ?_⟩
    -- the probability at the machine's clock is the probability at the padded time
    set T := c₁ * t a.length + c₂
    have hprob : ProbComp.eval (M.runClosed T a) = ProbComp.eval
        (M.runClosed (paddedTime τ) a) := by
      rcases le_total T (paddedTime τ) with hle | hle
      · exact (M.eval_runClosed_eq_of_halted a hle (hmem a).1).symm
      · exact M.eval_runClosed_eq_of_halted a hle ((halted_support_iff M a _).mpr hhalt)
    have hpT : 1 ≤ paddedTime τ := le_trans (by omega) (le_paddedTime τ)
    rw [(hmem a).2, hprob, one_div, MultiTapePTM.half_lt_eval_runClosed_apply_iff,
      eval_majorityProg hPMc hok]
    have e : paddedTime τ - 1 + 1 = paddedTime τ := by omega
    have := two_pow_lt_two_mul_iff (Z := M.acceptCount a (paddedTime τ)) (m := paddedTime τ - 1)
      (by rw [e]; exact acceptCount_le_two_pow)
    rw [e] at this
    rw [this, e]

/-- `PPTIME[t] ⊆ DSPACE[D ∘ t]` from the clocked bits at the scale `D`. -/
theorem pptime_subset_dspaceAt {D : ℕ → ℕ} (hDs : Scale D) (hB : ClockedBitsAt D) {t : ℕ → ℕ}
    (ht : ∀ n, n ≤ t n) : PPTIME encBits t ⊆ DSPACE encBits (fun n => D (t n)) := fun _ hA =>
  (pptime_decidedAt hDs hB ht hA).mem_DSPACE

/-- `BPTIME[t] ⊆ DSPACE[D ∘ t]` from the clocked bits at the scale `D`. -/
theorem bptime_subset_dspaceAt {D : ℕ → ℕ} (hDs : Scale D) (hB : ClockedBitsAt D) {t : ℕ → ℕ}
    (ht : ∀ n, n ≤ t n) : BPTIME encBits t ⊆ DSPACE encBits (fun n => D (t n)) :=
  BPTIME_subset_PPTIME.trans (pptime_subset_dspaceAt hDs hB ht)

/-! ### The endpoints from Theorem 2.3 at a scale `D` -/

section BlockBits

variable {D : ℕ → ℕ} (hDs : Scale D) (hc : CarryFits D) (hB : BlockBitsAt D)
include hDs hc hB

/-- **Theorem 1.1 at a scale `D`, from Theorem 2.3 at the scale `D`.** If the bits of the block
networks are computed in values below `2 ^ (C · D τ)`, then for every `t(n) ≥ n` every problem in
`NTIME[t]` is decided in simultaneous time `2 ^ (C · D (t n))` and space `C · D (t n)`. -/
theorem generalSimulationAt_of_blockBitsAt : GeneralSimulationAt D :=
  generalSimulationAt_of_clocked hDs
    (clockedCountingAt_of_clockedBitsAt hDs.log_le (clockedBitsAt_of_blockBitsAt hDs.log_le hc hB))

/-- `NTIME[t] ⊆ DSPACE[D ∘ t]` for every `t(n) ≥ n`, from Theorem 2.3 at the scale `D`. -/
theorem ntime_subset_dspace_of_blockBitsAt (t : ℕ → ℕ) (ht : ∀ n, n ≤ t n) :
    NTIME encBits t ⊆ DSPACE encBits (fun n => D (t n)) :=
  ntime_subset_dspace_of_generalAt (generalSimulationAt_of_blockBitsAt hDs hc hB) ht

/-- **Theorem 7.1 for `PPTIME` at a scale `D`, from Theorem 2.3 at the scale `D`**: for every
`t(n) ≥ n`, every problem in `PPTIME[t]` is decided in simultaneous time `2 ^ (C · D (t n))` and
space `C · D (t n)`. -/
theorem pptime_decidedAt_of_blockBitsAt {t : ℕ → ℕ} (ht : ∀ n, n ≤ t n) {A : Set (List Bool)}
    (hA : A ∈ PPTIME encBits t) : DecidedAt D t A :=
  pptime_decidedAt hDs (clockedBitsAt_of_blockBitsAt hDs.log_le hc hB) ht hA

/-- `PPTIME[t] ⊆ DSPACE[D ∘ t]` for every `t(n) ≥ n`, from Theorem 2.3 at the scale `D`. -/
theorem pptime_subset_dspace_of_blockBitsAt (t : ℕ → ℕ) (ht : ∀ n, n ≤ t n) :
    PPTIME encBits t ⊆ DSPACE encBits (fun n => D (t n)) :=
  pptime_subset_dspaceAt hDs (clockedBitsAt_of_blockBitsAt hDs.log_le hc hB) ht

/-- `BPTIME[t] ⊆ DSPACE[D ∘ t]` for every `t(n) ≥ n`, from Theorem 2.3 at the scale `D`. -/
theorem bptime_subset_dspace_of_blockBitsAt (t : ℕ → ℕ) (ht : ∀ n, n ≤ t n) :
    BPTIME encBits t ⊆ DSPACE encBits (fun n => D (t n)) :=
  bptime_subset_dspaceAt hDs (clockedBitsAt_of_blockBitsAt hDs.log_le hc hB) ht

end BlockBits

end Cslib.Complexity.NtimeDspace.Cross
