/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Nat.WeightedIndex
public import CslibFrontier.Init
public import Mathlib.Logic.Function.Iterate

/-!
# Counting walks with one matrix-entry query per iteration

A starting block and a sequence of generated letters select a trajectory through an integer-weighted
matrix. The evaluator walks through the blocks, their steps, and the columns of each row in a fixed
order. Each iteration receives one lower-level entry as its answer and retains seven natural
registers. The width represents the absorbing sink when its row has zero weight.
-/

public section

namespace Cslib.Probability.SaksZhou

open Finset

/-- Registers for the fixed-length sweep of starting blocks, generator steps and matrix columns. -/
structure SweepState where
  /-- Starting block index. -/
  x : ℕ
  /-- Position in the generated walk. -/
  t : ℕ
  /-- Current column, with markers for starting and ending a walk step. -/
  j : ℕ
  /-- State at the start of the step, with the width as sink. -/
  current : ℕ
  /-- First column that could still contain the label. -/
  candidate : ℕ
  /-- Part of the letter index remaining after skipped columns. -/
  residual : ℕ
  /-- Number of completed starting blocks ending at the requested column. -/
  hits : ℕ

/-- Start the first walk from `source`, before reading its first letter. -/
@[expose] def sweepStart (n source : ℕ) : SweepState := ⟨0, 0, n+1, source, 0, 0, 0⟩

/-- Consume one lower-level entry. The marker `n+1` starts a new block and column `n` ends it;
the marker `len` ends a seed. Each seed therefore makes exactly `(n+2)*len + 1` queries. -/
@[expose] def sweepUpdate (n len scale src dst : ℕ) (label : ℕ → ℕ → ℕ) (s : SweepState)
    (answer : ℕ) : SweepState :=
  if s.t = len then
    ⟨s.x+1, 0, n+1, src, 0, 0, s.hits + if s.current = dst then 1 else 0⟩
  else if s.j = n+1 then
    ⟨s.x, s.t, 0, s.current, 0, label s.x s.t, s.hits⟩
  else if s.j = n then
    ⟨s.x, s.t+1, n+1, s.candidate, 0, 0, s.hits⟩
  else if s.j = s.candidate ∧ answer * scale ≤ s.residual then
    ⟨s.x, s.t, s.j+1, s.current, s.candidate+1, s.residual-answer*scale, s.hits⟩
  else
    {s with j := s.j+1}

section Sweep

variable (n len scale src dst : ℕ) (label : ℕ → ℕ → ℕ) (counts : ℕ → ℕ → ℕ)

private def sweepAdvance (s : SweepState) : SweepState :=
  sweepUpdate n len scale src dst label s (counts s.current s.j)

local notation "advance" => (sweepAdvance n len scale src dst label counts)

private theorem sweep_columns (x t u j rem hits left : ℕ) (ht : t < len) (hj : j + left ≤ n) :
    advance^[left] ⟨x,t,j,u,j,rem,hits⟩ =
      let selected := scanWeightedRow left (fun q => counts u (j+q) * scale) rem
      ⟨x,t,j+left,u,j+selected,
        rem - ∑ q ∈ range selected, counts u (j+q) * scale,hits⟩ := by
  induction left generalizing j rem with
  | zero => simp [scanWeightedRow]
  | succ l ih =>
    have hjn : j < n := by omega
    rw [Function.iterate_succ_apply]
    simp only [sweepAdvance, sweepUpdate, ht.ne, hjn.ne, show j ≠ n+1 by omega, ite_false, true_and,
      scanWeightedRow, Nat.add_zero]
    by_cases h : rem < counts u j * scale
    · simp only [h, Nat.not_le.mpr h, ite_false, ite_true]
      have hfreeze (k : ℕ) (hk : j + 1 + k ≤ n) :
          advance^[k] ⟨x,t,j+1,u,j,rem,hits⟩ = ⟨x,t,j+1+k,u,j,rem,hits⟩ := by
        induction k with
        | zero => rfl
        | succ k ihk =>
          rw [Function.iterate_succ_apply', ihk (by omega)]
          simp only [sweepAdvance, sweepUpdate, ht.ne, show j+1+k ≠ n+1 by omega,
            show j+1+k ≠ n by omega, show j+1+k ≠ j by omega, false_and, ite_false]
          rfl
      rw [hfreeze l (by omega)]
      simp
      omega
    · simp only [h, Nat.le_of_not_lt h, ite_false, ite_true]
      rw [ih (j+1) (rem - counts u j * scale) (by omega)]
      simp only [Nat.add_assoc, Nat.add_comm 1, sum_range_succ', Nat.add_zero, Nat.sub_sub]
      congr 2 <;> omega

end Sweep

end Cslib.Probability.SaksZhou
