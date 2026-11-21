/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleEndpointQuery
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleEndpointAnswer
import Mathlib.Data.Nat.Size

/-!
# Length of a schedule endpoint answer

A successful query returns the number of an actual interval in the represented schedule.
Consequently even a linear scan of a long schedule yields a logarithmic-length answer.
This bounds the input to the subsequent arithmetic that constructs a pair of root vertices.
-/

public section

namespace Turing.MultiTapeTM.ScheduleEndpointQuery

/-- Every returned interval lies inside the raw schedule's represented horizon. -/
theorem found_lt_intervals (k : ℕ) (a : Input) {j : ℕ}
    (hq : query k a = some (some j)) : j < a.raw.length / (2 * (k + 1)) := by
  have hv : valid k a = true := by rw [← query_isSome, hq]; rfl
  obtain ⟨q, σ, i, h, d, rfl⟩ := exists_rows_of_valid k a hv
  rw [query_rows] at hq
  cases he : MultiTapePTM.firstAfter (MultiTapePTM.InWindow σ h
      (MultiTapePTM.portBlock σ i h d)) i with
  | none => simp [he] at hq
  | some v =>
    have hj : v.val = j := by simpa only [he, Option.map_some, Option.some.injEq] using hq
    have hlen : (ScheduleBits.rows (List.ofFn σ)).length / (2 * (k + 1)) = q := by simp
    change j < (ScheduleBits.rows (List.ofFn σ)).length / (2 * (k + 1))
    rw [hlen, ← hj]
    exact v.isLt

/-- Both tags and the canonical binary endpoint fit in the binary size of the raw length
plus two. The same estimate covers invalid requests and valid exhaustion. -/
theorem length_answer_le (k : ℕ) (a : Input) :
    (ScheduleEndpointAnswer.encAnswer (query k a)).length ≤ a.raw.length.size + 2 := by
  cases hq : query k a with
  | none => simp [ScheduleEndpointAnswer.encAnswer]
  | some answer =>
    cases answer with
    | none => simp [ScheduleEndpointAnswer.encAnswer]
    | some j =>
      have hj := found_lt_intervals k a hq
      have hs := Nat.size_le_size (hj.le.trans (Nat.div_le_self _ _))
      change ([true, true] ++ j.bits).length ≤ a.raw.length.size + 2
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.size_eq_bits_len]
      omega

end Turing.MultiTapeTM.ScheduleEndpointQuery
