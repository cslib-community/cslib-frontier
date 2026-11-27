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

## Main definitions

* `SweepState` stores the current seed, generator position, column, current state, candidate,
  residual label, and number of successful seeds.
* `sweepStart` initializes the first seed. `sweepUpdate` advances the sweep by one entry query.

## Main results

* `iterate_sweepUpdate_hits` identifies the final count with the number of walks reaching the
  specified destination.
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
@[expose] def sweepStart (n source : ℕ) : SweepState := ⟨0, 0, n + 1, source, 0, 0, 0⟩

/-- Begin the scan of one generated letter at column marker `n + 1` and end it at marker `n`.
The time marker `len` finalizes a starting seed. Marker iterations ignore the supplied entry. -/
@[expose] def sweepUpdate (n len scale src dst : ℕ) (label : ℕ → ℕ → ℕ) (s : SweepState)
    (answer : ℕ) : SweepState :=
  if s.t = len then
    ⟨s.x + 1, 0, n + 1, src, 0, 0, s.hits + if s.current = dst then 1 else 0⟩
  else if s.j = n + 1 then
    ⟨s.x, s.t, 0, s.current, 0, label s.x s.t, s.hits⟩
  else if s.j = n then
    ⟨s.x, s.t + 1, n + 1, s.candidate, 0, 0, s.hits⟩
  else if s.j = s.candidate ∧ answer * scale ≤ s.residual then
    ⟨s.x, s.t, s.j + 1, s.current, s.candidate + 1, s.residual - answer * scale, s.hits⟩
  else
    {s with j := s.j + 1}

section Sweep

variable (n len scale src dst : ℕ) (label : ℕ → ℕ → ℕ) (counts : ℕ → ℕ → ℕ)

private def sweepAdvance (s : SweepState) : SweepState :=
  sweepUpdate n len scale src dst label s (counts s.current s.j)

local notation "advance" => (sweepAdvance n len scale src dst label counts)

private theorem sweep_columns (x t u j rem hits left : ℕ) (ht : t < len) (hj : j + left ≤ n) :
    advance^[left] ⟨x, t, j, u, j, rem, hits⟩ =
      let selected := scanWeightedRow left (fun q => counts u (j + q) * scale) rem
      ⟨x, t, j + left, u, j + selected,
        rem - ∑ q ∈ range selected, counts u (j + q) * scale, hits⟩ := by
  induction left generalizing j rem with
  | zero => simp [scanWeightedRow]
  | succ l ih =>
    have hjn : j < n := by omega
    rw [Function.iterate_succ_apply]
    simp only [sweepAdvance, sweepUpdate, ht.ne, hjn.ne, show j ≠ n + 1 by omega, ite_false,
      true_and, scanWeightedRow, Nat.add_zero]
    by_cases h : rem < counts u j * scale
    · simp only [h, Nat.not_le.mpr h, ite_false, ite_true]
      have hfreeze (k : ℕ) (hk : j + 1 + k ≤ n) :
          advance^[k] ⟨x, t, j + 1, u, j, rem, hits⟩ = ⟨x, t, j + 1 + k, u, j, rem, hits⟩ := by
        induction k with
        | zero => rfl
        | succ k ihk =>
          rw [Function.iterate_succ_apply', ihk (by omega)]
          simp only [sweepAdvance, sweepUpdate, ht.ne, show j + 1 + k ≠ n + 1 by omega,
            show j + 1 + k ≠ n by omega, show j + 1 + k ≠ j by omega, false_and, ite_false]
          rfl
      rw [hfreeze l (by omega)]
      simp
      omega
    · simp only [h, Nat.le_of_not_lt h, ite_false, ite_true]
      rw [ih (j + 1) (rem - counts u j * scale) (by omega)]
      simp only [Nat.add_assoc, Nat.add_comm 1, sum_range_succ', Nat.add_zero, Nat.sub_sub]
      congr 2; omega

private theorem sweep_block (x t u hits : ℕ) (ht : t < len) :
    advance^[n + 2] ⟨x, t, n + 1, u, 0, 0, hits⟩ =
      ⟨x, t + 1, n + 1, scanWeightedRow n (fun j => counts u j * scale) (label x t),
        0, 0, hits⟩ := by
  rw [Function.iterate_succ_apply]
  simp only [sweepAdvance, sweepUpdate, ht.ne, ite_false, ite_true]
  rw [Function.iterate_succ_apply',
    sweep_columns n len scale src dst label counts x t u 0 (label x t) hits n ht (by omega)]
  simp [sweepAdvance, sweepUpdate, ht.ne]

private theorem sweep_blocks (x hits t : ℕ) (ht : t ≤ len) :
    advance^[(n + 2) * t] ⟨x, 0, n + 1, src, 0, 0, hits⟩ =
      ⟨x, t, n + 1, (List.range t).foldl
        (fun u t => scanWeightedRow n (fun j => counts u j * scale) (label x t)) src,
        0, 0, hits⟩ := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ, Nat.add_comm, Function.iterate_add_apply, ih (by omega),
      sweep_block _ _ _ _ _ _ _ _ _ _ _ (by omega), List.range_succ, List.foldl_append]
    rfl

/-- Over all starting blocks, the sweep counts precisely those whose walk ends at `dst`. The
query count per block depends only on the width and length and includes the finalization steps. -/
theorem iterate_sweepUpdate_hits (seeds : ℕ) :
    (((fun s : SweepState => sweepUpdate n len scale src dst label s (counts s.current s.j))^[
        seeds * ((n + 2) * len + 1)]) (sweepStart n src)).hits =
      ((List.range seeds).countP fun x => decide ((List.range len).foldl
        (fun u t => scanWeightedRow n (fun j => counts u j * scale) (label x t)) src = dst)) := by
  let reached x := (List.range len).foldl
    (fun u t => scanWeightedRow n (fun j => counts u j * scale) (label x t)) src
  have cells (y : ℕ) : advance^[y * ((n + 2) * len + 1)] (sweepStart n src) =
      ⟨y, 0, n + 1, src, 0, 0, (List.range y).countP fun x => decide (reached x = dst)⟩ := by
    induction y with
    | zero => simp [sweepStart]
    | succ y ih =>
      rw [Nat.succ_mul, Nat.add_comm, Function.iterate_add_apply, ih,
        Function.iterate_succ_apply', sweep_blocks _ _ _ _ _ _ _ _ _ _ le_rfl]
      simp [sweepAdvance, sweepUpdate, List.range_succ, reached]
  exact congrArg SweepState.hits (cells seeds)

end Sweep

end Cslib.Probability.SaksZhou
