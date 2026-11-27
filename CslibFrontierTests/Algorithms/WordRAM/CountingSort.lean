/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Algorithms.WordRAM.CountingSort
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize

/-!
# Client tests for `CslibFrontier.Algorithms.WordRAM.CountingSort`

Exercises `countingSortPure` (permutation, sortedness, equal-key stability), `countingSortProg_spec`
on stride-1 and stride-4 record arrays with equal keys, empty `count = 0` / `numKeys = 0` edge
cases, and composite `Realizes .exact` (`work = 0`) clients via `realize`.
-/

-- This test module intentionally exports no declarations.
set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.WordRAM.CountingSort

open Cslib.Algorithms.WordRAM
open Cslib.DataStructure
open Cslib.DataStructure.Memory
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ## 1. Pure reference model checks -/

example :
    countingSortPure 3 (fun p : ℕ × ℕ => p.1) [(2, 10), (0, 20), (2, 30), (1, 40)] =
      [(0, 20), (1, 40), (2, 10), (2, 30)] := by
  decide

example (xs : List (ℕ × ℕ)) (hbound : ∀ p ∈ xs, p.1 < 4) :
    (countingSortPure 4 (fun p => p.1) xs).Perm xs ∧
    (countingSortPure 4 (fun p => p.1) xs).Pairwise (fun a b => a.1 ≤ b.1) :=
  ⟨countingSortPure_perm 4 (fun p => p.1) xs hbound,
    countingSortPure_pairwise_key 4 (fun p => p.1) xs⟩

example (xs : List (ℕ × ℕ)) (hR : xs.Pairwise (fun a b => a.2 < b.2)) :
    (countingSortPure 4 (fun p => p.1) xs).Pairwise
      (fun a b => a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)) :=
  countingSortPure_stable 4 (fun p => p.1) hR

/-! ## 2. Stride-4 equal-key stability and `count = 0` / `numKeys = 0` boundary specs -/

private def r0 : Fin 4 → ℕ := ![7, 2, 10, 99]
private def r1 : Fin 4 → ℕ := ![8, 0, 20, 88]
private def r2 : Fin 4 → ℕ := ![9, 2, 30, 77]
private def r3 : Fin 4 → ℕ := ![6, 1, 40, 66]

example :
    let rows := [r0, r1, r2, r3]
    countingSortPure 3 (fun r => r 1) rows = [r1, r3, r0, r2] := by
  simp [countingSortPure, List.range_succ, r0, r1, r2, r3]

example {w inBase : ℕ} {rows : List (Fin 4 → ℕ)} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hxs : HoldsRecords 4 inBase rows s.mem)
    (hin : inBase + 4 * rows.length ≤ s.frontier)
    (hbound : ∀ r ∈ rows, r ⟨1, by decide⟩ < 3)
    (hfit : Fits w (s.frontier + 3 + 4 * rows.length)) :
    Memory.FramedTriple w s
      (countingSortProg ⟨3, rows.length, 4, 1, inBase⟩)
      (2 * (4 * rows.length) + 6 * rows.length + 11)
      ∅
      fun out s' =>
        out = ⟨s.frontier + 3, 4 * rows.length⟩ ∧
        out.Allocated s' ∧
        s'.frontier = s.frontier + 3 + 4 * rows.length ∧
        Memory.WellFormed w s' ∧
        HoldsRecords 4 out.base (countingSortPure 3 (fun r => r ⟨1, by decide⟩) rows) s'.mem := by
  simpa using countingSortProg_spec hwf hxs hin (by decide) hbound hfit

example {w inBase : ℕ} {rows : List (Fin 1 → ℕ)} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hxs : HoldsRecords 1 inBase rows s.mem)
    (hin : inBase + 1 * rows.length ≤ s.frontier)
    (hbound : ∀ r ∈ rows, r ⟨0, by decide⟩ < 5)
    (hfit : Fits w (s.frontier + 5 + 1 * rows.length)) :
    Memory.FramedTriple w s
      (countingSortProg ⟨5, rows.length, 1, 0, inBase⟩)
      (2 * (1 * rows.length) + 6 * rows.length + 17)
      ∅
      fun out s' =>
        out = ⟨s.frontier + 5, 1 * rows.length⟩ ∧
        out.Allocated s' ∧
        s'.frontier = s.frontier + 5 + 1 * rows.length ∧
        Memory.WellFormed w s' ∧
        HoldsRecords 1 out.base (countingSortPure 5 (fun r => r ⟨0, by decide⟩) rows) s'.mem := by
  simpa using countingSortProg_spec hwf hxs hin (by decide) hbound hfit

example {w : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s) (hfit : Fits w s.frontier) :
    Memory.FramedTriple w s (countingSortProg ⟨0, 0, 4, 0, 0⟩) 2 ∅
      fun out s' =>
        out = ⟨s.frontier, 0⟩ ∧ out.Allocated s' ∧ s'.frontier = s.frontier ∧
        Memory.WellFormed w s' ∧ HoldsRecords 4 out.base [] s'.mem := by
  simpa [countingSortPure] using countingSortProg_spec (numKeys := 0) (stride := 4) (keyOff := 0)
    (inBase := 0) (rows := []) hwf (HoldsRecords.nil 4 0 s.mem) (Nat.zero_le _) (by decide)
    (fun _ h => absurd h (List.not_mem_nil)) (by simpa using hfit)

/-! ## 3. Composite `Realizes .exact` client calling `countingSortProg` -/

private def sortAndReadFirstKeyProg (a : CountingSortArgs) : Memory.Prog ℕ := do
  let out ← countingSortProg a
  Memory.read (out.base + a.keyOff)

example : Realizes .exact sortAndReadFirstKeyProg countingSortArgsWords WordEncoding.encode
    (fun w a s =>
      0 < a.count ∧
      a.keyOff < a.stride ∧
      a.inBase + a.stride * a.count ≤ s.frontier ∧
      Fits w (s.frontier + a.numKeys + a.stride * a.count) ∧
      ∀ i < a.count, s.mem (a.inBase + a.stride * i + a.keyOff) < a.numKeys)
    (fun _ _ => 0) := by
  unfold sortAndReadFirstKeyProg
  realize [realizes_countingSortProg]
  all_goals
    obtain ⟨hpos, hkey, hin, hfit, hbound⟩ := h
    have hspec : ((Memory.spec 0).clientState s (countingSortProg d)).frontier =
          s.frontier + d.numKeys + d.stride * d.count ∧
        ((Memory.spec 0).clientResult s (countingSortProg d)).base = s.frontier + d.numKeys := by
      let rows : List (Fin d.stride → ℕ) :=
        List.ofFn fun i : Fin d.count => fun j : Fin d.stride =>
          s.mem (d.inBase + d.stride * i.val + j.val)
      have hlen : rows.length = d.count := List.length_ofFn
      have hxs : HoldsRecords d.stride d.inBase rows s.mem := by
        intro i hi j; simp [rows]
      have hbd : ∀ r ∈ rows, r ⟨d.keyOff, hkey⟩ < d.numKeys := by
        intro r hr; rw [List.mem_ofFn] at hr; obtain ⟨i, rfl⟩ := hr; exact hbound i.val i.isLt
      have hft := countingSortProg_spec hmem hxs (by simpa [hlen] using hin) hkey hbd
        (by simpa [hlen] using hfit)
      have hd : (⟨d.numKeys, rows.length, d.stride, d.keyOff, d.inBase⟩ : CountingSortArgs) =
          d := by
        cases d; simpa using hlen
      obtain ⟨_, _, _, hout, _, hfr, _, _⟩ := framedTriple_iff_realization.mp hft
      rw [hd] at hout hfr
      exact ⟨by simpa [hlen] using hfr, by simp [hout]⟩
    first
    | exact hkey
    | exact hin
    | exact hfit
    | exact hbound
    | exact (hfit.of_le (by
        rw [hspec.2]
        have hmul : d.stride ≤ d.stride * d.count := Nat.le_mul_of_pos_right d.stride hpos
        omega))

end CslibFrontierTests.Algorithms.WordRAM.CountingSort
