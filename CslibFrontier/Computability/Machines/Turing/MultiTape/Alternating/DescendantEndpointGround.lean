/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.DescendantEndpointTerminal
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TwoWordPredicate

/-!
# A finite native terminal on protected descendant storage

The two stored words are the original raw schedule and one short descendant endpoint position.
The native terminal serializes them once, then computes the actual root lookup or closed local
verdict. Its clock is linear in the raw schedule and polynomial in the short position and binary
schedule length.
-/

public section

namespace Turing.MultiTapeATM.DescendantEndpointTerminal

open MultiTapeTM DescendantEndpoint

/-- One fixed finite terminal works for every runtime schedule and position. -/
theorem exists_evaluator (k : ℕ) :
    ∃ (U : ℕ) (schedule query : Fin U) (S : Type) (_ : Finite S)
      (atm : MultiTapeATM U Bool S) (C d : ℕ), schedule ≠ query ∧
      ∀ (input raw : List Bool) (p : Position),
        let start := (TwoWordInput.ready schedule query input raw (encPosition p)).withState
          (some atm.toPTM.initial)
        let time := C * (raw.length + shortSize (raw, p) ^ d + 1)
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔ check k (raw, p) = true) := by
  obtain ⟨d, hc⟩ := exists_computableInO k
  obtain ⟨U, schedule, query, S, hS, atm, c, hne, hrun⟩ :=
    TwoWordPredicate.exists_of_inO hc
  refine ⟨U, schedule, query, S, hS, atm, 4 * c, max 1 d, hne, ?_⟩
  intro input raw p start time
  have hs := hrun input raw p
  have hsize : 1 ≤ shortSize (raw, p) := by dsimp [shortSize]; omega
  have hlinear : shortSize (raw, p) ≤ shortSize (raw, p) ^ max 1 d := by
    simpa only [pow_one] using Nat.pow_le_pow_right hsize (Nat.le_max_left 1 d)
  have hpower : shortSize (raw, p) ^ d ≤ shortSize (raw, p) ^ max 1 d :=
    Nat.pow_le_pow_right hsize (Nat.le_max_right 1 d)
  have htime : c * ((encInput (raw, p)).length +
      (raw.length + shortSize (raw, p) ^ d) + 1) ≤ time := by
    have hlen : (encPosition p).length ≤ shortSize (raw, p) := by
      dsimp [shortSize]; omega
    have hbase : (encInput (raw, p)).length +
        (raw.length + shortSize (raw, p) ^ d) + 1 ≤
        4 * (raw.length + shortSize (raw, p) ^ max 1 d + 1) := by
      simp only [encInput, length_encPair, encBits_apply]
      omega
    calc
      _ ≤ c * (4 * (raw.length + shortSize (raw, p) ^ max 1 d + 1)) :=
        Nat.mul_le_mul_left c hbase
      _ = time := by dsimp [time]; ring
  exact ⟨hs.1.mono htime, ⟨fun h => hs.2.mp (h.of_halted_stepCoins hs.1),
    fun h => (hs.2.mpr h).mono htime⟩⟩

end Turing.MultiTapeATM.DescendantEndpointTerminal
