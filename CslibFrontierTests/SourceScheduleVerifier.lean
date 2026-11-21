/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.SourceScheduleVerifier

/-!
# Public regressions for outer count initialization from the ordinary input
-/

open Turing Turing.MultiTapeTM Turing.MultiTapeATM
open Cslib.Complexity.CountingSimulation Cslib.Circuits.Boolean.CarryLookahead.Query

-- Empty schedule: one possible path, binary height zero and empty unary frontier.
example : (ScheduleFields.expanded ⟨0, ⟨1, 0, true⟩⟩).count = 1 := by decide
example : ScheduleFields.word .unary ⟨0, ⟨1, 0, false⟩⟩ = [] := by decide

-- A six-bit movement schedule has exactly 64 leaves. Build the word even when the claim is false.
example : ScheduleFields.word (.stored .count) ⟨3, ⟨17, 2, false⟩⟩ =
    [false, false, false, false, false, false, true] := by decide

-- Every legal bit, including the most significant one, satisfies the same setup clock.
example (k c d : ℕ) : ∃ K, ∀ {t : ℕ}, 2 ≤ t →
    ∀ (bit : Fin (paddedTime t + 1)) (sign : Bool),
      c * (ScheduleFields.budget d (scheduleRequest k t bit sign) + 1) ≤
        K * (numBlocks t + 1) := exists_scheduleField_clock k c d

-- Exercise the ordinary configuration and its physical pair encoding through the public API.
example (k s K : ℕ) (R : Type) [Finite R] (i j : Fin K) (hne : i ≠ j)
    (right : MultiTapeATM K Bool R) :
    ∃ (u : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM u Bool Q) (C t₀ : ℕ),
      ∀ (S : Type) [Finite S] (M : MultiTapePTM k Bool S) (st : S ≃ Fin s)
        (input : List Bool) {t : ℕ}, t₀ ≤ t → ∀ budget,
        ChecksSeededContractions i j right M st input t budget →
        ∀ (bit : Fin (paddedTime t + 1)) (claim : Bool),
        let clock := C * (input.length + (t / (Nat.log 2 (t + 2)).sqrt + 2)) + budget
        let p : ScheduleChallenge := ⟨t, bit, claim⟩
        let cfg := atm.toPTM.toNTM.initCfg (encPair ScheduleChallenge.enc encBits (p, input))
        atm.HaltsWithin clock cfg ∧ (atm.AcceptsWithin clock cfg ↔
          (M.acceptCount input (paddedTime t)).testBit bit = claim) := by
  obtain ⟨u, Q, hQ, atm, C, t₀, h⟩ := exists_source_count_verifier k s i j hne right
  exact ⟨u, Q, hQ, atm, C, t₀, fun _ _ M => h M⟩
