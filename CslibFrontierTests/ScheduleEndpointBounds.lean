/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleEndpointBounds

import Mathlib.Data.Nat.Size

open Turing.MultiTapeTM ScheduleEndpointQuery ScheduleEndpointAnswer

-- Even with arbitrary selector and interval fields, a million-bit table yields at most 23 bits.
example (k : ℕ) (a : Input) (ha : a.raw.length = 2 ^ 20) :
    (encAnswer (query k a)).length ≤ 23 := by
  have h := length_answer_le k a
  rw [ha, Nat.size_pow] at h
  exact h

example (k : ℕ) (a : Input) {j : ℕ} (hj : a.raw.length / (2 * (k + 1)) ≤ j) :
    query k a ≠ some (some j) := by
  intro h
  have := found_lt_intervals k a h
  omega
