/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.ShortScheduleVerifier
public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.ScheduleChallenge
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SourceWordInput

/-!
# Outer schedule verification from the ordinary input tape

The input consists of a framed binary challenge followed by the source word. The simulator
physically splits the input, preserves the source for use as a virtual read-only tape, computes
the short parameters and context, and constructs every outer counting field. Its remaining
premise is a finite contraction continuation for balanced seeds.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM _root_.Turing.MultiTapeATM
open CarryLookaheadCountingInitialLayout OuterRootLeaf

/-- Start the count verifier with just the binary clock, index and sign on one work tape. -/
theorem exists_challenge_verifier (k states : ℕ) {K : ℕ} {R : Type} [Finite R]
    (i j : Fin K) (hij : i ≠ j) (right : MultiTapeATM K Bool R) :
    ∃ (u : ℕ) (src : Fin u) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM u Bool Q) (C t₀ : ℕ),
      ∀ {State : Type} [Finite State] (M : MultiTapePTM k Bool State) (st : State ≃ Fin states)
        (input : List Bool) {t : ℕ}, t₀ ≤ t → ∀ budget,
        ChecksSeededContractions i j right M st input t budget →
        ∀ (bit : Fin (paddedTime t + 1)) (claim : Bool),
        let p : ScheduleChallenge := ⟨t, bit.val, claim⟩
        let start := SharedWordFork.start src atm input (ScheduleChallenge.enc p) 0
        let time := C * (t / (Nat.log 2 (t + 2)).sqrt + 2) + budget
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          (M.acceptCount input (paddedTime t)).testBit bit.val = claim) := by
  obtain ⟨scratch, a, r, q, S, hS, eval, C, t₀, he⟩ :=
    exists_short_count_verifier k states i j hij right
  let := hS
  obtain ⟨d, hf, hg⟩ := ScheduleChallenge.exists_setup_degree k states
  obtain ⟨u, src, Q, hQ, atm, c, h⟩ :=
    TwoWordLoad.exists_load_from hf hg _ _
      (CarryLookaheadCountingPrepare.context_ne_request scratch a r q) eval
  obtain ⟨B, hB⟩ := ScheduleChallenge.exists_clock c d
  refine ⟨u, src, Q, hQ, atm, B + C, max 2 t₀, ?_⟩
  intro State _ M st input t ht budget hseed bit claim p start time
  let eTime := C * (t / (Nat.log 2 (t + 2)).sqrt + 2) + budget
  obtain ⟨hh, ha⟩ := he M st input ((Nat.le_max_right _ _).trans ht) budget hseed bit claim
  have hs := h input p 0 (Nat.zero_le _) eTime
  dsimp only at hs
  rw [CarryLookaheadCountingPrepare.ready_eq_initial] at hs
  obtain ⟨hh₁, ha₁⟩ := hs hh
  have hb := (hB p ((Nat.le_max_left _ _).trans ht) bit.isLt).trans
    (Nat.mul_le_mul_left B (Nat.succ_le_succ (numBlocks_le_div_sqrt_log_add_one t)))
  change c * (((ScheduleChallenge.enc p).length + 1) ^ d + 1) + 8 ≤
    B * (t / (Nat.log 2 (t + 2)).sqrt + 2) at hb
  have hc : 0 + c * (((ScheduleChallenge.enc p).length + 1) ^ d + 1) + 8 + eTime ≤ time := by
    dsimp only [time, eTime]
    rw [Nat.add_mul]
    omega
  exact ⟨hh₁.mono hc, ⟨fun h' => ha.mp (ha₁.mp (h'.of_halted_stepCoins hh₁)),
    fun h' => (ha₁.mpr (ha.mpr h')).mono hc⟩⟩

/-- From the ordinary framed input with every work tape blank, count verification costs one
source scan, the square-root-logarithmic overhead and one seeded contraction on each branch. -/
theorem exists_source_count_verifier (k states : ℕ) {K : ℕ} {R : Type} [Finite R]
    (i j : Fin K) (hij : i ≠ j) (right : MultiTapeATM K Bool R) :
    ∃ (u : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM u Bool Q) (C t₀ : ℕ),
      ∀ {State : Type} [Finite State] (M : MultiTapePTM k Bool State) (st : State ≃ Fin states)
        (input : List Bool) {t : ℕ}, t₀ ≤ t → ∀ budget,
        ChecksSeededContractions i j right M st input t budget →
        ∀ (bit : Fin (paddedTime t + 1)) (claim : Bool),
        let p : ScheduleChallenge := ⟨t, bit.val, claim⟩
        let start := atm.toPTM.toNTM.initCfg (encPair ScheduleChallenge.enc encBits (p, input))
        let time := C * (input.length + (t / (Nat.log 2 (t + 2)).sqrt + 2)) + budget
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          (M.acceptCount input (paddedTime t)).testBit bit.val = claim) := by
  obtain ⟨v, src, S, hS, child, A, t₀, hv⟩ := exists_challenge_verifier k states i j hij right
  let := hS
  obtain ⟨u, Q, hQ, atm, c, h⟩ := SourceWordInput.exists_prepend ScheduleChallenge.enc src child
  obtain ⟨G, hG⟩ := ScheduleChallenge.exists_clock 1 1
  refine ⟨u, Q, hQ, atm, c + c * G + A, max 2 t₀, ?_⟩
  intro State _ M st input t ht budget hseed bit claim p start time
  let m := t / (Nat.log 2 (t + 2)).sqrt + 2
  let ct := A * m + budget
  obtain ⟨hh, ha⟩ := hv M st input ((Nat.le_max_right _ _).trans ht) budget hseed bit claim
  obtain ⟨hh₁, ha₁⟩ := h p input ct hh
  have hx := (hG p ((Nat.le_max_left _ _).trans ht) bit.isLt).trans
    (Nat.mul_le_mul_left G (Nat.succ_le_succ (numBlocks_le_div_sqrt_log_add_one t)))
  change 1 * (((ScheduleChallenge.enc p).length + 1) ^ 1 + 1) + 8 ≤ G * m at hx
  simp only [one_mul, pow_one] at hx
  have hlen : (ScheduleChallenge.enc p).length + 1 ≤ G * m := by omega
  have hc : c * (input.length + (ScheduleChallenge.enc p).length + 1) + ct ≤ time := by
    let N := c + c * G + A
    have h₁ : c * input.length ≤ N * input.length :=
      Nat.mul_le_mul_right _ (by dsimp [N]; omega)
    have h₂ : (c * G + A) * m ≤ N * m := Nat.mul_le_mul_right _ (by dsimp [N]; omega)
    calc
      _ ≤ c * (input.length + G * m) + ct := by rw [Nat.add_assoc]; gcongr
      _ = c * input.length + (c * G + A) * m + budget := by dsimp only [ct]; ring
      _ ≤ N * (input.length + m) + budget := by
        rw [Nat.mul_add N input.length m]
        exact Nat.add_le_add_right (Nat.add_le_add h₁ h₂) _
  exact ⟨hh₁.mono hc, ⟨fun h' => ha.mp (ha₁.mp (h'.of_halted_stepCoins hh₁)),
    fun h' => (ha₁.mpr (ha.mpr h')).mono hc⟩⟩

end Cslib.Complexity.CountingSimulation
