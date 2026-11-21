/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.SeededRawScheduleVerifier
public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.ScheduleFieldClock
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.ScheduleCountPrepare

/-!
# The signed counting machine from short parameters

Only the context and the small binary record are initially present. This machine restores all
seven fields, checks its branch of the outer schedule sum, and runs the seeded root verifier.
The remaining hypothesis is the continuation on a balanced contraction seed. The native field
preparation, outer sum and shared-seed fork collectively pay its time once on each branch.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM _root_.Turing.MultiTapeATM
open OuterRootLeaf

/-- A bounded seeded contraction continuation suffices for the outer count from short tapes. -/
theorem exists_short_count_verifier (k states : ℕ) {K : ℕ} {R : Type} [Finite R]
    (i j : Fin K) (hij : i ≠ j) (right : MultiTapeATM K Bool R) :
    ∃ (scratch a r q : ℕ) (Q : Type) (_ : Finite Q)
      (atm : MultiTapeATM (CarryLookaheadCountingPrepare.size scratch a r q) Bool Q) (C t₀ : ℕ),
      ∀ {State : Type} [Finite State] (M : MultiTapePTM k Bool State) (st : State ≃ Fin states)
        (input : List Bool) {t : ℕ}, t₀ ≤ t → ∀ budget,
        ChecksSeededContractions i j right M st input t budget →
        ∀ (bit : Fin (paddedTime t + 1)) (claim : Bool),
        let context := RootBalanceRequest.encPublic (outerRootTemplate k states t)
        let request := scheduleRequest k t bit.val claim
        let start := (CarryLookaheadCountingPrepare.initial scratch a r q input context request)
          |>.withState (some atm.toPTM.initial)
        let time := C * (t / (Nat.log 2 (t + 2)).sqrt + 2) + budget
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          (M.acceptCount input (paddedTime t)).testBit bit.val = claim) := by
  obtain ⟨a, r, q, S, hS, eval, C, t₀, he⟩ := exists_seeded_count_verifier k states i j hij right
  let := hS
  obtain ⟨scratch, Q, hQ, atm, c, d, hh⟩ := ScheduleCountPrepare.exists_prepend eval
  obtain ⟨B, hB⟩ := exists_scheduleField_clock k c d
  refine ⟨scratch, a, r, q, Q, hQ, atm, B + C, max 2 t₀, ?_⟩
  intro State _ M st input t ht budget hseed bit claim ctx req start time
  let eTime := C * (t / (Nat.log 2 (t + 2)).sqrt + 2) + budget
  obtain ⟨hhalt, hacc⟩ := he M st input ((Nat.le_max_right _ _).trans ht) budget hseed bit claim
  have hw : (ScheduleFields.expanded req).count = 2 ^ (2 * (k + 1) * numBlocks t) := by
    simp [req, ScheduleFields.expanded, scheduleRequest, Nat.mul_assoc]
  have hc := hh input ctx req eTime
  dsimp only at hc
  rw [hw] at hc
  obtain ⟨hh₁, ha₁⟩ := hc hhalt
  have hb := (hB ((Nat.le_max_left _ _).trans ht) bit claim).trans
    (Nat.mul_le_mul_left B (Nat.succ_le_succ (numBlocks_le_div_sqrt_log_add_one t)))
  change c * (ScheduleFields.budget d req + 1) ≤ B * (t / (Nat.log 2 (t + 2)).sqrt + 2) at hb
  have hclock : c * (ScheduleFields.budget d req + 1) + eTime ≤ time := by
    dsimp only [time, eTime]
    rw [Nat.add_mul]
    omega
  exact ⟨hh₁.mono hclock, ⟨fun h => hacc.mp (ha₁.mp (h.of_halted_stepCoins hh₁)),
    fun h => (ha₁.mpr (hacc.mpr h)).mono hclock⟩⟩

end Cslib.Complexity.CountingSimulation
