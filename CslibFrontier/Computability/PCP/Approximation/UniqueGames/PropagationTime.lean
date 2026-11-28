/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Approximation.UniqueGames.Propagation
public import CslibFrontier.Computability.WordRAM.ListOutput
public import CslibFrontier.Computability.PCP.Approximation.UniqueGames.PropagationTime.Model
import CslibFrontier.Computability.PCP.Approximation.UniqueGames.PropagationTime.SetupBuckets
import CslibFrontier.Computability.PCP.Approximation.UniqueGames.PropagationTime.Steps
import CslibFrontier.Computability.PCP.Approximation.UniqueGames.PropagationTime.ExtractCheck

/-!
# Word-RAM label propagation for unique games

`Cslib.Complexity.UniqueGames.Propagation.program` and
`Cslib.Complexity.UniqueGames.Propagation.decideProgram` implement the label-propagation algorithm
`Cslib.Complexity.UniqueGames.Propagation.solve` [Khot, Section 2.4][Khot2010] as a uniform
`Basis.standard` word-RAM program over finite label sets `Fin L` (`[NeZero L]`).

Every operation of the algorithm is executed and charged in word-RAM step semantics:
* scanning the input edges to compute `N = slots g` (`O(|E|)` instructions);
* building per-slot linked incidence lists in memory representing `buckets N g.edges` (`O(|E|)`
  instructions, relying on zero-initialized cells above the input for empty list heads);
* outer iteration over edges, initializing each unvisited seed's table and candidate array (`O(L)`),
  exploring its connected component via an explicit stack in memory (`O(L)` per incident edge for
  forward composition, first-preimage inversion, backward composition, and candidate pruning), and
  freezing every slot of the component to the first surviving guess (`O(L)` per slot);
* extracting the final labelling into the output array (`O(N)`) and checking every edge (`O(|E|)`).

On an instance `g : Graph (Fin L → Fin L)` (`[NeZero L]`) with `N = slots g` vertex slots and
`E = g.edges.length` edges, at any word width `w` satisfying `Fits w (wordBound g)`, both programs
halt in at most `timeBound g` (`O(L · (N + E))`) instructions: `program` outputs
`encodeSolution (slots g) (solve (List.finRange L) g)` via `ExecutesList` (from which
`decodeSolution L` recovers `solve (List.finRange L) g` identically), and `decideProgram` outputs
`(solve (List.finRange L) g).isSome.toNat` via `Executes`.

This module re-exports the pure incidence-list and encoding API from `PropagationTime.Model` and
composes the privately imported symbolic-execution phases (`SetupBuckets`, `Steps` — joining the
parallel `Extend`, `StartPrune`, and `Settle` leaves — and `ExtractCheck`) into `solveCode`,
`program`, and `decideProgram` without leaking internal register or layout declarations.

## Main definitions

* `Cslib.Complexity.UniqueGames.Propagation.insertEdge`,
  `Cslib.Complexity.UniqueGames.Propagation.buckets`: pure incidence-list construction
  (re-exported from `PropagationTime.Model`).
* `Cslib.Complexity.UniqueGames.Propagation.encodeEdge`,
  `Cslib.Complexity.UniqueGames.Propagation.encode`: flat word-RAM input encoding of
  `Graph (Fin L → Fin L)` (re-exported from `PropagationTime.Model`).
* `Cslib.Complexity.UniqueGames.Propagation.encodeSolution`,
  `Cslib.Complexity.UniqueGames.Propagation.decodeSolution`: list-output encoding and exact decoder
  for `Option (ℕ → Fin L)` (re-exported from `PropagationTime.Model`).
* `Cslib.Complexity.UniqueGames.Propagation.wordBound`,
  `Cslib.Complexity.UniqueGames.Propagation.timeBound`: word-width and `O(L · (slots g + |E|))`
  instruction bounds (re-exported from `PropagationTime.Model`).
* `Cslib.Complexity.UniqueGames.Propagation.Reg.outBase`,
  `Cslib.Complexity.UniqueGames.Propagation.Reg.ok`: output-array address and decision registers
  (re-exported from `PropagationTime.Model`).
* `Cslib.Complexity.UniqueGames.Propagation.solveCode`,
  `Cslib.Complexity.UniqueGames.Propagation.program`,
  `Cslib.Complexity.UniqueGames.Propagation.decideProgram`: structured and flat word-RAM programs.

## Main results

* `Cslib.Complexity.UniqueGames.Propagation.buckets_spec`,
  `Cslib.Complexity.UniqueGames.Propagation.buckets_getD`: `buckets` computes `adj g`
  (re-exported from `PropagationTime.Model`).
* `Cslib.Complexity.UniqueGames.Propagation.decodeSolution_encodeSolution`: `decodeSolution`
  recovers `solve (List.finRange L) g` from `encodeSolution`
  (re-exported from `PropagationTime.Model`).
* `Cslib.Complexity.UniqueGames.Propagation.Fits.inputFits_encode`: fitting `wordBound g` suffices
  for `InputFits w (encode g)` (re-exported from `PropagationTime.Model`).
* `Cslib.Complexity.UniqueGames.Propagation.solveCode_spec`: structured `ExecWithin` specification
  for `solveCode` certifying both `Reg.ok` and the `outputList` at `Reg.outBase`.
* `Cslib.Complexity.UniqueGames.Propagation.program_spec`,
  `Cslib.Complexity.UniqueGames.Propagation.program_spec_of_wellFormed`,
  `Cslib.Complexity.UniqueGames.Propagation.computesListInTime_program`: `ExecutesList` and
  `Program.ComputesListInTime` certificates for full assignment recovery.
* `Cslib.Complexity.UniqueGames.Propagation.decideProgram_spec`,
  `Cslib.Complexity.UniqueGames.Propagation.computesInTime_decideProgram`: `Executes` and
  `Program.ComputesInTime` certificates for satisfiability / `solve.isSome`.

## References

* [S. Khot, *On the Unique Games Conjecture*, Section 2.4][Khot2010]
-/

public section

namespace Cslib.Complexity.UniqueGames.Propagation

open Cslib.PCP Cslib.PCP.Encoded Cslib.WordRAM Reg

/-- Structured word-RAM program running label propagation on `encode g`: leaves the base address of
`encodeSolution (slots g) (solve (List.finRange L) g)` in `Reg.outBase` and
`(solve (List.finRange L) g).isSome.toNat` in `Reg.ok`. -/
def solveCode : Code .standard 34 :=
  setupCode.seq
    (bucketsLoop.seq
      (resetStateCode.seq
        (stepsLoop.seq
          (extractCode.seq
            (checkCode.seq finishCode)))))

/-- Flat word-RAM program halting with the address `Reg.outBase` of the length-prefixed solution
`encodeSolution (slots g) (solve (List.finRange L) g)`. -/
def program : Program .standard 34 :=
  solveCode.program outBase

/-- Flat word-RAM program halting with `(solve (List.finRange L) g).isSome.toNat` in `Reg.ok`. -/
def decideProgram : Program .standard 34 :=
  solveCode.program ok

/-- **Structured Word-RAM specification for `solveCode`:** from `Data.init (encode g)` at any
width `w` fitting `wordBound g`, `solveCode` terminates in at most `timeBound g - 1` steps with
`Reg.ok` equal to `(solve (List.finRange L) g).isSome.toNat` and `outputList` at `Reg.outBase`
equal to `encodeSolution (slots g) (solve (List.finRange L) g)` (whose end address fits in `w`). -/
theorem solveCode_spec {L w : ℕ} [NeZero L] (g : Graph (Fin L → Fin L))
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w solveCode (Data.init (encode g)) y (timeBound g - 1) ∧
      y.regs ok = (solve (List.finRange L) g).isSome.toNat ∧
      outputList y.mem (y.regs outBase) =
        encodeSolution (slots g) (solve (List.finRange L) g) ∧
      Fits w (y.regs outBase + (encodeSolution (slots g) (solve (List.finRange L) g)).length) := by
  obtain ⟨x1, hx1, hc1, hinp1, hnf1, hidx1, hzero1⟩ := slotsSetup_spec (w := w) g hw
  obtain ⟨x2, hx2, hc2, hinp2, hbkt2, hzero2⟩ :=
    bucketsLoop_spec (w := w) g hc1 hinp1 hnf1 hidx1 hzero1 hw
  obtain ⟨x3, hx3, hT3, hidx3⟩ :=
    resetStateCode_spec (w := w) g x2 hc2 hinp2 hbkt2 hzero2
  obtain ⟨x4, hx4, hT4⟩ := stepsLoop_spec (w := w) g x3 hT3 hidx3 hw
  obtain ⟨x5, hx5, hc5, hinp5, hout5⟩ := extractCode_spec (w := w) g x4 hT4 hw
  obtain ⟨x6, hx6, hc6, hok6, hm6⟩ := checkCode_spec (w := w) g x5 hc5 hinp5 hout5 hw
  obtain ⟨y, hx7, _, hokY, houtList, hfitOut⟩ :=
    finishCode_spec (w := w) g x6 hc6 hok6 (hm6 ▸ hout5) hw
  have htot_le :
      16 * g.edges.length + 30 +
        (g.edges.length * 28 + 2 +
          (3 +
            ((5 * L + 38) * slots g + (106 * L + 152) * g.edges.length + 2 +
              (slots g * 12 + 3 + (g.edges.length * 19 + 4 + 6))))) ≤
        timeBound g - 1 := by
    rw [show timeBound g - 1 =
      (16 * L + 80) * slots g + (120 * L + 300) * g.edges.length + 79 by
      simp only [timeBound]; omega]
    nlinarith
  have htot : ExecWithin w solveCode (Data.init (encode g)) y (timeBound g - 1) :=
    (hx1.seq (hx2.seq (hx3.seq (hx4.seq (hx5.seq (hx6.seq hx7)))))).mono htot_le
  exact ⟨y, htot, hokY, houtList, hfitOut⟩

/-- **Word-RAM label propagation (`ExecutesList`).** On any instance `g : Graph (Fin L → Fin L)`
(`[NeZero L]`) and any word width `w` fitting `wordBound g`, `program` halts in at most
`timeBound g` (`O(L · (slots g + |g.edges|))`) instructions and outputs
`encodeSolution (slots g) (solve (List.finRange L) g)`. -/
theorem program_spec {L w : ℕ} [NeZero L] (g : Graph (Fin L → Fin L))
    (hw : Fits w (wordBound g)) :
    ∃ n ≤ timeBound g,
      ExecutesList w program (.init (encode g))
        (encodeSolution (slots g) (solve (List.finRange L) g)) n := by
  obtain ⟨y, ⟨m, hm, he⟩, _, hout, hfit⟩ := solveCode_spec (w := w) g hw
  have hpos : 1 ≤ timeBound g := by simp only [timeBound]; omega
  exact ⟨m + 1, by omega, hout ▸ he.executesList outBase (by rwa [hout])⟩

/-- **Word-RAM label propagation on well-formed instances (`slots g = g.vertices`).** -/
theorem program_spec_of_wellFormed {L w : ℕ} [NeZero L] {g : Graph (Fin L → Fin L)}
    (hg : g.WellFormed) (hw : Fits w (wordBound g)) :
    ∃ n ≤ (16 * L + 80) * g.vertices + (120 * L + 300) * g.edges.length + 80,
      ExecutesList w program (.init (encode g))
        (encodeSolution g.vertices (solve (List.finRange L) g)) n := by
  simpa only [timeBound, slots_eq_vertices hg] using program_spec (w := w) g hw

/-- `program` uniformly computes `encodeSolution (slots g) (solve (List.finRange L) g)` in
`timeBound g` instructions at every width `w` fitting `wordBound g`. -/
theorem computesListInTime_program (L : ℕ) [NeZero L] :
    program.ComputesListInTime (fun _ (g : Graph (Fin L → Fin L)) => encode g)
      (fun g _ => timeBound g) (fun g w => Fits w (wordBound g))
      (fun g => encodeSolution (slots g) (solve (List.finRange L) g)) :=
  fun g _ hw _ => (program_spec g hw).elim fun n ⟨hn, hex⟩ => ⟨n, hex, hn⟩

/-- **Word-RAM label propagation decision certificate (`Executes`).** On any instance
`g : Graph (Fin L → Fin L)` (`[NeZero L]`) and any word width `w` fitting `wordBound g`,
`decideProgram` halts in at most `timeBound g` instructions and outputs
`(solve (List.finRange L) g).isSome.toNat`. -/
theorem decideProgram_spec {L w : ℕ} [NeZero L] (g : Graph (Fin L → Fin L))
    (hw : Fits w (wordBound g)) :
    ∃ n ≤ timeBound g,
      Executes w decideProgram (.init (encode g))
        (solve (List.finRange L) g).isSome.toNat n := by
  obtain ⟨y, ⟨m, hm, he⟩, hok, _, _⟩ := solveCode_spec (w := w) g hw
  have hpos : 1 ≤ timeBound g := by simp only [timeBound]; omega
  exact ⟨m + 1, by omega, hok ▸ he.executes ok⟩

/-- `decideProgram` uniformly computes `(solve (List.finRange L) g).isSome.toNat` in `timeBound g`
instructions at every width `w` fitting `wordBound g`. -/
theorem computesInTime_decideProgram (L : ℕ) [NeZero L] :
    decideProgram.ComputesInTime (fun _ (g : Graph (Fin L → Fin L)) => encode g)
      (fun g _ => timeBound g) (fun g w => Fits w (wordBound g))
      (fun g => (solve (List.finRange L) g).isSome.toNat) :=
  fun g _ hw _ => (decideProgram_spec g hw).elim fun n ⟨hn, hex⟩ => ⟨n, hex, hn⟩

end Cslib.Complexity.UniqueGames.Propagation
