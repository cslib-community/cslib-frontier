/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PP.Time
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ClockSearch
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ClockedPrograms
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.HaltCount

/-!
# Theorem 7.1 for `PPTIME` and `BPTIME`

For every `t(n) ≥ n`, a problem in Complexitylib's `PPTIME[t]` (strict majority of the fair-coin
runs within `O(t)`, ties rejecting) is decided in simultaneous time `2^(C·SqrtLog t(n))` and space
`C·SqrtLog t(n)`, given the clocked bits (`ClockedBits`, `pptime_decided`). The decider tries the
clocks `τ = (n + K₀) 2^j`; at each it reads bit `paddedTime τ` of the accept count of the halt
marker of the machine (all runs have halted), and at the first clock where every run has halted
it decides by the comparison `2^T < 2 · acceptCount` at `T = paddedTime τ`, read from three bits
and one test on the lower bits (`majorityProg`). Since `BPTIME ⊆ PPTIME`, the same holds for
`BPTIME[t]`. With `ClockedResidues` (a residue form of Theorem 2.3) this is Theorem 7.1 for
these classes (`pptime_subset_dspace`, `bptime_subset_dspace`).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross

open NtimeDspace.ProgLang Exact Cslib Cslib.Complexity Cslib.Complexity.CountingSimulation
  _root_.Turing _root_.Turing.MultiTapeTM

/-- Decided in simultaneous time `2^(C·SqrtLog t(n))` and space `C·SqrtLog t(n)`. -/
def DecidedInSqrtLog (t : ℕ → ℕ) (A : Set (List Bool)) : Prop :=
  ∃ C, DecidableInTimeAndSpace A encBits (fun a => 2 ^ (C * SqrtLog (t a.length)))
    (fun a => C * SqrtLog (t a.length))

theorem DecidedInSqrtLog.mem_DSPACE {t : ℕ → ℕ} {A : Set (List Bool)}
    (h : DecidedInSqrtLog t A) : A ∈ DSPACE encBits (fun n => SqrtLog (t n)) := by
  obtain ⟨C, hC⟩ := h
  exact mem_DSPACE_iff.mpr ⟨C, 0, _, hC⟩

section Halting

variable {k : ℕ} {State : Type} (M : MultiTapePTM k Bool State) (input : List Bool)

/-- Halting of every run within a clock, in Complexitylib's distributional form, is halting of
every coin replay. -/
theorem halted_support_iff (T : ℕ) :
    (∀ final ∈ (ProbComp.eval (M.runClosedConfigFrom T (M.initialConfig input))).support,
        final.tapes.state = none) ↔
      ∀ coins : List Bool, coins.length = T →
        (M.stepCoins coins (Cfg.init M.initial input)).state = none := by
  rw [MultiTapePTM.eval_runClosedConfigFrom_eq_map_coins, PMF.support_map]
  simp only [Set.mem_image, BitString.mem_support_uniformList_iff, forall_exists_index, and_imp]
  constructor
  · intro h coins hc
    have := h _ coins hc rfl
    rwa [MultiTapePTM.tapes_runClosedConfigFromCoins] at this
  · rintro h _ coins hc rfl
    rw [MultiTapePTM.tapes_runClosedConfigFromCoins]
    exact h coins hc

/-- Halting persists at longer clocks. -/
theorem halted_mono {T T' : ℕ} (hT : T ≤ T')
    (h : ∀ coins : List Bool, coins.length = T →
      (M.stepCoins coins (Cfg.init M.initial input)).state = none) :
    ∀ coins : List Bool, coins.length = T' →
      (M.stepCoins coins (Cfg.init M.initial input)).state = none := by
  intro coins hc
  have hh := h (coins.take T) (by simp [hc, hT])
  rw [← List.take_append_drop T coins, HaltCount.stepCoins_append_of_halted M _ _ hh]
  exact hh

end Halting

/-- The bits program of a table, at a valid clock. -/
theorem bitsOK_of {k : ℕ} {State : Type} {M : MultiTapePTM k Bool State} {P : Prog} {C τ₀ : ℕ}
    (hP : ∀ (w : List Bool) (τ j : ℕ), w.length ≤ τ → τ₀ ≤ τ →
      P.eval w [τ, w.length, j] = M.acceptCount w (paddedTime τ) / 2 ^ j % 2 ∧
        P.Bounded w (2 ^ (C * SqrtLog τ)) [τ, w.length, j])
    {w : List Bool} {τ : ℕ} (hw : w.length ≤ τ) (hτ : τ₀ ≤ τ) {D : ℕ} (hD : C ≤ D) :
    BitsOK w P τ w.length (M.acceptCount w (paddedTime τ)) (2 ^ (D * SqrtLog τ)) := fun j =>
  ⟨(hP w τ j hw hτ).1, bounded_mono (Nat.pow_le_pow_right (by norm_num)
    (Nat.mul_le_mul_right _ hD)) _ _ (hP w τ j hw hτ).2⟩

theorem two_mul_add_two_le {τ D : ℕ} (hD : 2 ≤ D) : 2 * τ + 2 ≤ 2 ^ (D * SqrtLog τ) := by
  have hτS : τ < 2 ^ SqrtLog τ := lt_two_pow_sqrtLog τ
  have hS : 1 ≤ SqrtLog τ := Nat.le_add_left _ _
  have : 2 ^ (SqrtLog τ + 1) ≤ 2 ^ (D * SqrtLog τ) :=
    Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  rw [pow_succ] at this
  omega

/-- **Theorem 7.1 for `PPTIME`**, from the clocked bits: for every `t(n) ≥ n`, a
problem decided by strict majority within `O(t)` is decided in simultaneous time
`2^(C·SqrtLog t(n))` and space `C·SqrtLog t(n)`. -/
theorem pptime_decided (hB : ClockedBits) {t : ℕ → ℕ} (ht : ∀ n, n ≤ t n) {A : Set (List Bool)}
    (hA : A ∈ PPTIME encBits t) : DecidedInSqrtLog t A := by
  classical
  obtain ⟨c₁, c₂, k, State, hfin, M, hM⟩ := hA
  obtain ⟨PM, CM, τM, hPMc, hPM⟩ := hB k State M
  obtain ⟨PH, CH, τH, hPHc, hPH⟩ := hB k State (HaltCount.haltMark M)
  have hmem := fun a => (hM a)
  simp only [encBits_apply] at hmem
  refine decidable_of_clockedTests ht A (bitAtPad PH) (majorityProg PM) (CH + 2) (CM + 2)
    (max (max τM τH) 2) c₁ c₂ ?_ ?_ ?_
  · intro a τ ha hτ
    exact bounded_bitAtPad hPHc (bitsOK_of hPH ha (by omega) (by omega)) (by omega)
      (two_mul_add_two_le (by omega))
  · intro a τ ha hτ hT
    rw [eval_bitAtPad hPHc (bitsOK_of hPH ha (by omega) (D := CH + 2) (by omega))]
    refine (eq_two_pow_iff_bit acceptCount_le_two_pow).mp ?_
    rw [HaltCount.acceptCount_haltMark_eq_two_pow_iff]
    exact halted_mono M a (hT.trans (le_paddedTime τ))
      ((halted_support_iff M a _).mp (hmem a).1)
  · intro a τ ha hτ hpos
    have hhalt : ∀ coins : List Bool, coins.length = paddedTime τ →
        (M.stepCoins coins (Cfg.init M.initial a)).state = none := by
      rw [eval_bitAtPad hPHc (bitsOK_of hPH ha (by omega) (D := CH + 2) (by omega)),
        ← eq_two_pow_iff_bit acceptCount_le_two_pow,
        HaltCount.acceptCount_haltMark_eq_two_pow_iff] at hpos
      exact hpos
    have hok := bitsOK_of hPM ha (by omega) (D := CM + 2) (by omega)
    refine ⟨bounded_majorityProg hPMc hok (by omega) (two_mul_add_two_le (by omega)), ?_⟩
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

/-- **Theorem 7.1 for `PPTIME`**, as a space class. -/
theorem pptime_subset_dspace (hB : ClockedBits) {t : ℕ → ℕ} (ht : ∀ n, n ≤ t n) :
    PPTIME encBits t ⊆ DSPACE encBits (fun n => SqrtLog (t n)) := fun _ hA =>
  (pptime_decided hB ht hA).mem_DSPACE

/-- **Theorem 7.1 for `BPTIME`** ("and hence `BPTIME`"): bounded error is a strict majority. -/
theorem bptime_subset_dspace (hB : ClockedBits) {t : ℕ → ℕ} (ht : ∀ n, n ≤ t n) :
    BPTIME encBits t ⊆ DSPACE encBits (fun n => SqrtLog (t n)) :=
  BPTIME_subset_PPTIME.trans (pptime_subset_dspace hB ht)

/-- `PPTIME[t] ⊆ DSPACE[t/√log t]` from a residue form of Theorem 2.3 at an arbitrary clock. -/
theorem pptime_subset_dspace_of_residues (hR : ClockedResidues) {t : ℕ → ℕ}
    (ht : ∀ n, n ≤ t n) : PPTIME encBits t ⊆ DSPACE encBits (fun n => SqrtLog (t n)) :=
  pptime_subset_dspace (clockedBits_of_clockedResidues hR) ht

/-- `BPTIME[t] ⊆ DSPACE[t/√log t]` from a residue form of Theorem 2.3 at an arbitrary clock. -/
theorem bptime_subset_dspace_of_residues (hR : ClockedResidues) {t : ℕ → ℕ}
    (ht : ∀ n, n ≤ t n) : BPTIME encBits t ⊆ DSPACE encBits (fun n => SqrtLog (t n)) :=
  bptime_subset_dspace (clockedBits_of_clockedResidues hR) ht

end Cslib.Complexity.NtimeDspace.Cross
