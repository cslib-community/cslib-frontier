/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Complexity.Classes.Space.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.QueryLoop
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Tactic.Space

/-!
# A loop over the input, certified without declaring a query machine

Counting the ones of a word in binary, and deciding whether they are the majority, in logarithmic
space: the loop is `Turing.MultiTapeTM.ComputableInSpace.queryLoop_of_invariant`, its round is
certified by `space`, and the only hand-written parts are the invariant of the scan and the size of
its state.
-/

open Turing Turing.MultiTapeTM

namespace SpaceQueryLoopTest

/-- The state of the scan: the position, the number of ones before it, and whether the end of the
word has been reached. -/
structure Scan where
  /-- The position of the next bit. -/
  pos : ℕ
  /-- The number of ones before `pos`. -/
  ones : ℕ
  /-- Whether the end of the word has been reached. -/
  finished : Bool

enc_structure encScan : Scan where pos : encNat, ones : encNat, finished : encBool

/-- A round: count the bit read, or finish past the end of the word. -/
def next (p : Scan × Option Bool) : Scan :=
  if p.2.isSome then ⟨p.1.pos + 1, p.1.ones + (if p.2.getD false then 1 else 0), false⟩
  else ⟨p.1.pos, p.1.ones, true⟩

theorem next_inSpace : ComputableInSpace next (QueryMachine.encStateRead encScan) encScan
    fun p => (QueryMachine.encStateRead encScan p).length := by
  space [next]

theorem pos_inSpace : ComputableInSpace Scan.pos encScan encNat fun s => (encScan s).length := by
  space

theorem finished_inSpace :
    ComputableInSpace Scan.finished encScan encBool fun s => (encScan s).length := by
  space

/-- The invariant of the scan on `w`: the ones before the position are counted, the scan
finishes at the end of the word, and the variant counts the rounds left. -/
def Inv (w : List Bool) (m : ℕ) (s : Scan) : Prop :=
  s.pos ≤ w.length ∧ s.ones = (w.take s.pos).count true ∧
    (s.finished = true → s.pos = w.length) ∧
    m + s.pos = w.length + if s.finished then 0 else 1

theorem inv_round {w : List Bool} {m : ℕ} {s : Scan} (h : Inv w m s) (hf : s.finished = false) :
    ∃ m' < m, Inv w m' (queryRound Scan.pos next w s) := by
  obtain ⟨pos, ones, finished⟩ := s
  obtain ⟨hpos, hones, -, hm⟩ := h
  simp only at hf hpos hones hm
  subst hf hones
  simp only [Bool.false_eq_true, ↓reduceIte] at hm
  refine ⟨m - 1, by omega, ?_⟩
  rcases Nat.lt_or_ge pos w.length with hlt | hge
  · have htake := List.take_succ_eq_append_getElem hlt
    have hnext : queryRound Scan.pos next w ⟨pos, (w.take pos).count true, false⟩ =
        ⟨pos + 1, (w.take (pos + 1)).count true, false⟩ := by
      cases hb : w[pos] <;> simp [queryRound, next, List.getElem?_eq_getElem hlt, hb, htake]
    rw [hnext]
    exact ⟨hlt, rfl, by simp, by simp only [Bool.false_eq_true, ↓reduceIte]; omega⟩
  · have hnext : queryRound Scan.pos next w ⟨pos, (w.take pos).count true, false⟩ =
        ⟨pos, (w.take pos).count true, true⟩ := by
      simp [queryRound, next, List.getElem?_eq_none hge]
    rw [hnext]
    exact ⟨hpos, rfl, fun _ => Nat.le_antisymm hpos hge, by simp only [↓reduceIte]; omega⟩

theorem length_encScan_le {n : ℕ} {s : Scan} (hp : s.pos ≤ n) (ho : s.ones ≤ n) :
    (encScan s).length ≤ 7 * (0 + Nat.log2 n + 1) := by
  have h₁ := length_encNat_le_log2 hp
  have h₂ := length_encNat_le_log2 ho
  simp only [encScan_apply, encScanFields, length_encPair, encBool_apply, List.length_singleton]
  omega

/-- The final state of the scan, in logarithmic space. -/
theorem scan_inSpace : ComputableInSpace
    (fun w : List Bool => (⟨w.length, w.count true, true⟩ : Scan)) encBits encScan
    fun w => 0 + Nat.log2 w.length := by
  refine ComputableInSpace.queryLoop_of_invariant (start := fun _ => ⟨0, 0, false⟩)
    (fun w m s => Inv w m s) (ComputableInSpace.constZero _) pos_inSpace next_inSpace
    finished_inSpace (fun w => ⟨w.length + 1, by simp [Inv]⟩)
    (fun w m s h hf => inv_round h hf) (fun w m s h hf => ?_) ⟨7, fun w m s h => ?_⟩
  · obtain ⟨-, hones, hfin, -⟩ := h
    obtain ⟨pos, ones, finished⟩ := s
    obtain rfl : finished = true := hf
    obtain rfl : pos = w.length := hfin rfl
    simp only [List.take_length] at hones
    rw [hones]
  · rw [encBits_apply]
    exact length_encScan_le h.1 (h.2.1.trans_le
      (((List.take_sublist _ w).count_le true).trans List.count_le_length))

/-- **The number of ones of a word**, in binary, is computable within logarithmic space. -/
theorem count_inSpace : ComputableInSpace (fun w : List Bool => w.count true) encBits encNat
    fun w => Nat.log2 w.length :=
  (encScan_ones_budget scan_inSpace).mono_le fun w => by omega

/-- Majority is decided within logarithmic space. -/
theorem majority_inSpace :
    ComputableInSpace (fun w : List Bool => decide (w.length < 2 * w.count true)) encBits encBool
      fun w => Nat.log2 w.length := by
  have hlen : ComputableInSpace (fun w : List Bool => w.length) encBits encNat
      fun w => Nat.log2 w.length :=
    (encScan_pos_budget scan_inSpace).mono_le fun w => by omega
  have hcount := count_inSpace
  space

/-- Majority, in logarithmic space and in `DSPACE(log n)`. -/
example : ComputableInLogSpace (fun w : List Bool => decide (w.length < 2 * w.count true))
    encBits encBool :=
  majority_inSpace.computableInLogSpace

example : {w : List Bool | decide (w.length < 2 * w.count true) = true} ∈
    Cslib.Complexity.DSPACE encBits Nat.log2 :=
  Cslib.Complexity.setOf_mem_DSPACE_of_computableInSpace majority_inSpace fun _ => le_rfl

end SpaceQueryLoopTest
