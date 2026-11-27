/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.WordRAM.Realization.NatLog
public import CslibFrontier.Computability.WordRAM.Realization.RecordOps
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.NormNum

/-!
# Client tests for `LoopFrame` `ℚ`-potential rules and `Realization.RecordOps`

Exercises `iterate_rat_witness_spec`, `boundedWhile_rat_witness_spec`, `HoldsRecords`,
`concatRecordsProg` (non-empty and empty slices), `natLog2Prog`, and `iterLogProg`.
-/

-- This test module intentionally exports no declarations.
set_option linter.privateModule false

namespace CslibFrontierTests.Computability.WordRAM.Realization.RecordLoopOps

open Cslib.DataStructure
open Cslib.DataStructure.Memory
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ## 1. `iterate_rat_witness_spec` with fractional `ℚ` witness potential -/

private def toggleStep (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let v ← Memory.read (d.1 + d.2)
  if v = 0 then
    pure (d.2 + 1)
  else
    Memory.write (d.1 + d.2) 0
    pure (d.2 + 1)

example {w base n : ℕ} {s₀ : Memory.State} (hbound : base + n ≤ s₀.frontier) :
    ∃ w' : ℕ,
      let prog := iterate toggleStep base n 0
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
      Memory.Modifies (Set.Ico base (base + n)) s₀ ((Memory.spec 0).clientState s₀ prog) ∧
      (memoryCost prog s₀ : ℚ) + ((n - w' : ℕ) : ℚ) * (1 / 2 : ℚ) ≤
        ((n : ℕ) : ℚ) * (1 / 2 : ℚ) + (5 / 2 : ℚ) * (n : ℚ) := by
  let S : Set ℕ := Set.Ico base (base + n)
  let I (k widx idx : ℕ) (t : Memory.State) : Prop :=
    k ≤ n ∧ widx = k ∧ idx = k ∧ t.frontier = s₀.frontier
  let pot (_ : ℕ) (widx : ℕ) : ℚ := ((n - widx : ℕ) : ℚ) * (1 / 2 : ℚ)
  have hstep : ∀ k < n, ∀ widx idx t, I k widx idx t →
      (fun _ _ _ => True) w (base, idx) t ∧
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (toggleStep (base, idx))) ∧
      ∃ w' : ℕ,
        I (k + 1) w' ((Memory.spec 0).clientResult t (toggleStep (base, idx)))
          ((Memory.spec 0).clientState t (toggleStep (base, idx))) ∧
        (memoryCost (toggleStep (base, idx)) t : ℚ) + pot (k + 1) w' ≤ pot k widx + (5 / 2 : ℚ) ∧
        Memory.Modifies S t ((Memory.spec 0).clientState t (toggleStep (base, idx))) := by
    intro k hk widx idx t ⟨_, hwidx, hidx, htfr⟩
    subst widx idx
    have hft : Memory.FramedTriple w t (toggleStep (base, k)) 2 S
        fun res t' => res = k + 1 ∧ t'.frontier = s₀.frontier := by
      dsimp only [toggleStep]
      refine Memory.FramedTriple.read_bind (by rw [htfr]; omega) ?_
      split_ifs with hv
      · exact Memory.FramedTriple.mono (Memory.FramedTriple.pure (c := 0) ⟨rfl, htfr⟩) (by omega)
          fun _ _ h => h
      · refine Memory.FramedTriple.write_bind_of_mem (by rw [htfr]; omega) (fits_zero w)
          ⟨Nat.le_add_right _ _, by omega⟩ ?_
        exact Memory.FramedTriple.pure ⟨rfl, htfr⟩
    rw [framedTriple_iff_realization] at hft
    obtain ⟨hv, hcost, hmod, hres, htfr'⟩ := hft
    refine ⟨trivial, hv, k + 1, ⟨hk, rfl, hres, htfr'⟩, ?_, hmod⟩
    have hcost_q : (memoryCost (toggleStep (base, k)) t : ℚ) ≤ 2 := by exact_mod_cast hcost
    have hpot : pot (k + 1) (k + 1) + (1 / 2 : ℚ) = pot k k := by
      dsimp only [pot]
      have hsub : n - k = (n - (k + 1)) + 1 := by omega
      rw [hsub]
      push_cast
      ring
    linarith
  obtain ⟨_, hv, hmod, w', _, hcost⟩ :=
    iterate_rat_witness_spec toggleStep (fun _ _ _ => True) w base (5 / 2 : ℚ) n
      I pot S hstep 0 0 s₀ ⟨Nat.zero_le n, rfl, rfl, rfl⟩
  exact ⟨w', hv, hmod, by simpa [pot] using hcost⟩

/-! ## 2. `boundedWhile_rat_witness_spec` with fractional `ℚ` rank potential -/

private def stepReadGuard (d : ℕ × ℕ) (i : ℕ) : Prop := i < d.2

private instance (d : ℕ × ℕ) (i : ℕ) : Decidable (stepReadGuard d i) :=
  inferInstanceAs (Decidable (i < d.2))

private def stepReadBody (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let _ ← Memory.read (d.1.1 + d.2)
  pure (d.2 + 1)

example {w base n : ℕ} {s₀ : Memory.State} (hbound : base + n ≤ s₀.frontier) :
    ∃ w' : ℕ,
      let prog := boundedWhile stepReadGuard stepReadBody (base, n) n 0
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
      (memoryCost prog s₀ : ℚ) + ((n - w' : ℕ) : ℚ) * (1 / 2 : ℚ) ≤
        ((n : ℕ) : ℚ) * (1 / 2 : ℚ) + (1 / 2 : ℚ) * (n : ℚ) := by
  let I (widx idx : ℕ) (t : Memory.State) : Prop :=
    idx ≤ n ∧ widx = idx ∧ t.frontier = s₀.frontier
  let rank (widx : ℕ) : ℕ := n - widx
  let pot (widx : ℕ) : ℚ := ((n - widx : ℕ) : ℚ) * (1 / 2 : ℚ)
  have hzero : ∀ widx idx t, I widx idx t → rank widx = 0 → ¬stepReadGuard (base, n) idx := by
    intro widx idx t ⟨hle, hwidx, _⟩ hr hg
    change idx < n at hg
    dsimp only [rank] at hr
    omega
  have hstep : ∀ widx idx t, I widx idx t → stepReadGuard (base, n) idx →
      (fun _ _ _ => True) w ((base, n), idx) t ∧
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (stepReadBody ((base, n), idx))) ∧
      ∃ w' : ℕ,
        I w' ((Memory.spec 0).clientResult t (stepReadBody ((base, n), idx)))
          ((Memory.spec 0).clientState t (stepReadBody ((base, n), idx))) ∧
        (memoryCost (stepReadBody ((base, n), idx)) t : ℚ) + pot w' ≤ pot widx + (1 / 2 : ℚ) ∧
        Memory.Modifies ∅ t ((Memory.spec 0).clientState t (stepReadBody ((base, n), idx))) ∧
        rank w' < rank widx := by
    intro widx idx t ⟨hle, hwidx, htfr⟩ hg
    change idx < n at hg
    subst hwidx
    refine ⟨trivial, ?_, widx + 1, ⟨hg, rfl, htfr⟩, ?_, Memory.Modifies.refl ∅ t, ?_⟩
    · dsimp only [stepReadBody]
      exact validHistory_read_bind (by rw [htfr]; omega) (validHistory_pure w t (widx + 1))
    · have hcost : memoryCost (stepReadBody ((base, n), widx)) t = 1 := by
        dsimp only [stepReadBody]
        rw [memoryCost_bind', memoryCost_read, memoryCost_pure]
      rw [hcost]
      dsimp only [pot]
      have hsub : n - widx = (n - (widx + 1)) + 1 := by omega
      rw [hsub]
      push_cast
      linarith
    · dsimp only [rank]; omega
  obtain ⟨_, hv, _, _, w', _, hcost⟩ :=
    boundedWhile_rat_witness_spec stepReadGuard stepReadBody (fun _ _ _ => True) w (base, n)
      (1 / 2 : ℚ) (by norm_num) I rank pot ∅ hzero hstep n 0 0 s₀
      ⟨Nat.zero_le n, rfl, rfl⟩ (by simp [rank])
  exact ⟨w', hv, by simpa [pot, rank] using hcost⟩

/-! ## 3. `HoldsRecords`, `concatRecordsProg`, `natLog2Prog`, and `iterLogProg` -/

example {w stride srcA srcB srcC : ℕ} {rowsA rowsB rowsC : List (Fin stride → ℕ)}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hA : HoldsRecords stride srcA rowsA s.mem)
    (hA_lt : srcA + stride * rowsA.length ≤ s.frontier)
    (hB : HoldsRecords stride srcB rowsB s.mem)
    (hB_lt : srcB + stride * rowsB.length ≤ s.frontier)
    (hC : HoldsRecords stride srcC rowsC s.mem)
    (hC_lt : srcC + stride * rowsC.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + stride * (rowsA.length + rowsB.length + rowsC.length))) :
    Memory.FramedTriple w s
      (concatRecordsProg
        ⟨stride, srcA, rowsA.length, srcB, rowsB.length, srcC, rowsC.length⟩)
      (2 * (stride * (rowsA.length + rowsB.length + rowsC.length)) + 1)
      ∅
      fun out s' =>
        out = ⟨s.frontier, stride * (rowsA.length + rowsB.length + rowsC.length)⟩ ∧
        out.Allocated s' ∧
        s'.frontier = s.frontier + stride * (rowsA.length + rowsB.length + rowsC.length) ∧
        Memory.WellFormed w s' ∧
        HoldsRecords stride out.base (rowsA ++ rowsB ++ rowsC) s'.mem :=
  concatRecordsProg_spec hwf hA hA_lt hB hB_lt hC hC_lt hfit

example {w : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s) (hfit : Fits w s.frontier) :
    Memory.FramedTriple w s (concatRecordsProg ⟨4, 0, 0, 0, 0, 0, 0⟩) 1 ∅
      fun out s' =>
        out = ⟨s.frontier, 0⟩ ∧ out.Allocated s' ∧ s'.frontier = s.frontier ∧
        Memory.WellFormed w s' ∧ HoldsRecords 4 out.base ([] ++ [] ++ []) s'.mem := by
  simpa using concatRecordsProg_spec (stride := 4) (srcA := 0) (srcB := 0) (srcC := 0)
    (rowsA := []) (rowsB := []) (rowsC := []) hwf (HoldsRecords.nil 4 0 s.mem) (Nat.zero_le _)
    (HoldsRecords.nil 4 0 s.mem) (Nat.zero_le _) (HoldsRecords.nil 4 0 s.mem) (Nat.zero_le _)
    (by simpa using hfit)

example : Realizes .exact concatRecordsProg concatRecordsArgsWords WordEncoding.encode
    (fun w a s =>
      Fits w (a.lenA + a.lenB + a.lenC) ∧
      a.srcA + a.stride * a.lenA ≤ s.frontier ∧
      a.srcB + a.stride * a.lenB ≤ s.frontier ∧
      a.srcC + a.stride * a.lenC ≤ s.frontier)
    (fun _ _ => 0) :=
  realizes_concatRecordsProg

example (w : ℕ) (s : Memory.State) :
    Memory.FramedTriple w s (natLog2Prog 0) 0 ∅ (fun res s' => s' = s ∧ res = 0) ∧
    Memory.FramedTriple w s (natLog2Prog 1) 0 ∅ (fun res s' => s' = s ∧ res = 0) ∧
    Memory.FramedTriple w s (natLog2Prog 2) 0 ∅ (fun res s' => s' = s ∧ res = 1) ∧
    Memory.FramedTriple w s (natLog2Prog 16) 0 ∅ (fun res s' => s' = s ∧ res = 4) ∧
    Memory.FramedTriple w s (iterLogProg 0 16) 0 ∅ (fun res s' => s' = s ∧ res = 16) ∧
    Memory.FramedTriple w s (iterLogProg 1 16) 0 ∅ (fun res s' => s' = s ∧ res = 4) ∧
    Memory.FramedTriple w s (iterLogProg 2 16) 0 ∅ (fun res s' => s' = s ∧ res = 2) ∧
    Memory.FramedTriple w s (iterLogProg 3 16) 0 ∅ (fun res s' => s' = s ∧ res = 1) ∧
    Memory.FramedTriple w s (iterLogProg 4 16) 0 ∅ (fun res s' => s' = s ∧ res = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [show Nat.log 2 0 = 0 from rfl] using natLog2Prog_spec w 0 s
  · simpa [show Nat.log 2 1 = 0 from rfl] using natLog2Prog_spec w 1 s
  · simpa [show Nat.log 2 2 = 1 from by decide] using natLog2Prog_spec w 2 s
  · simpa [show Nat.log 2 16 = 4 from by decide] using natLog2Prog_spec w 16 s
  · exact iterLogProg_spec w 0 16 s
  · simpa [Nat.iterLog_succ_apply, show Nat.log 2 16 = 4 from by decide] using
      iterLogProg_spec w 1 16 s
  · simpa [Nat.iterLog_succ_apply, show Nat.log 2 16 = 4 from by decide,
      show Nat.log 2 4 = 2 from by decide] using iterLogProg_spec w 2 16 s
  · simpa [Nat.iterLog_succ_apply, show Nat.log 2 16 = 4 from by decide,
      show Nat.log 2 4 = 2 from by decide, show Nat.log 2 2 = 1 from by decide] using
      iterLogProg_spec w 3 16 s
  · simpa [Nat.iterLog_succ_apply, show Nat.log 2 16 = 4 from by decide,
      show Nat.log 2 4 = 2 from by decide, show Nat.log 2 2 = 1 from by decide,
      show Nat.log 2 1 = 0 from rfl] using iterLogProg_spec w 4 16 s

private def iterLogAndConcatProg (k : ℕ) (a : ConcatRecordsArgs) : Memory.Prog (ℕ × Block) := do
  let lg ← iterLogProg k a.lenA
  let blk ← concatRecordsProg a
  pure (lg, blk)

example : Realizes .exact (fun (k, a) => iterLogAndConcatProg k a)
    (appendWords (WordEncoding.encode (α := ℕ)) concatRecordsArgsWords)
    (WordEncoding.encode (α := ℕ × Block))
    (fun w (_, a) s =>
      Fits w 1 ∧
      Fits w (a.lenA + a.lenB + a.lenC) ∧
      a.srcA + a.stride * a.lenA ≤ s.frontier ∧
      a.srcB + a.stride * a.lenB ≤ s.frontier ∧
      a.srcC + a.stride * a.lenC ≤ s.frontier)
    (fun (k, a) _ => k * (Nat.log 2 a.lenA + 3)) := by
  have hraw : Realizes .exact (fun q : ℕ × ConcatRecordsArgs => iterLogAndConcatProg q.1 q.2)
      (appendWords (WordEncoding.encode (α := ℕ)) concatRecordsArgsWords)
      (WordEncoding.encode (α := ℕ × Block))
      (fun w q s =>
        Fits w 1 ∧
        Fits w (q.2.lenA + q.2.lenB + q.2.lenC) ∧
        q.2.srcA + q.2.stride * q.2.lenA ≤ s.frontier ∧
        q.2.srcB + q.2.stride * q.2.lenB ≤ s.frontier ∧
        q.2.srcC + q.2.stride * q.2.lenC ≤ s.frontier)
      (fun q _ => q.1 * (Nat.log 2 q.2.lenA + 3)) := by
    unfold iterLogAndConcatProg
    realize [realizes_iterLogProg, realizes_concatRecordsProg]
    all_goals
      obtain ⟨h1, hlen, hA, hB, hC⟩ := h
      have hs_it : (Memory.spec 0).clientState s (iterLogProg d.1 d.2.lenA) = s :=
        (framedTriple_iff_realization.mp (iterLogProg_spec 0 d.1 d.2.lenA s)).2.2.2.1
      simp only [hs_it] at *
      first
      | exact h1
      | exact hlen
      | exact hA
      | exact hB
      | exact hC
  exact hraw.congr (fun ⟨_, _⟩ => rfl)

end CslibFrontierTests.Computability.WordRAM.Realization.RecordLoopOps
