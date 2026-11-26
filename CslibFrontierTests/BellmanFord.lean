/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.Lean.BellmanFord.Basic
public import CslibFrontier.Algorithms.WordRAM.BellmanFord
public meta import CslibFrontier.Algorithms.WordRAM.BellmanFord
meta import CslibFrontier.Computability.WordRAM.Structured.FastEval
public import Mathlib.Algebra.Order.Group.Int

/-!
# The Bellman–Ford algorithm: worked examples

Kernel-checked examples (no `native_decide`): a negative edge with no negative cycle (correct
distances, `⊤` for an unreachable vertex), parallel edges between the same endpoints, a reachable
negative cycle (`none` / `[]`), a negative cycle that is not reachable from the source (distances
still returned), a negative self-loop, and word-RAM execution within `64 * n * (n + m)`
instructions.
-/

public section

namespace CslibFrontierTests.BellmanFord

open Cslib.Algorithms.Lean.BellmanFord
open Cslib.Algorithms.WordRAM.BellmanFord
open Cslib.WordRAM

private meta def runSolver (G : Instance) (w : ℕ) : Option (List ℕ × Bool) :=
  (solver.eval w w (Data.init G.encode)).map fun (y, t) =>
    (outputList y.mem G.outAddrBase, decide (t < 64 * G.n * (G.n + G.m)))

/-! ### A negative edge, no negative cycle -/

/-- `0 → 1` (weight `4`), `0 → 2` (`5`), `2 → 1` (`-3`); vertex `3` is unreachable. -/
def g : Fin 4 → List (Fin 4 × ℤ)
  | 0 => [(1, 4), (2, 5)]
  | 2 => [(1, -3)]
  | _ => []

example : (bellmanFord g (List.finRange 4) 0).map (fun d => (d 0, d 1, d 2, d 3)) =
    some (0, 2, 5, ⊤) := by decide +kernel

/-- The shortest walk to `1` goes through `2` and has weight `2`. -/
example : IsShortestDist g 0 1 2 := by
  obtain ⟨d, hd⟩ : ∃ d, bellmanFord g (List.finRange 4) 0 = some d ∧ d 1 = 2 :=
    ⟨_, rfl, by decide +kernel⟩
  exact hd.2 ▸ isShortestDist_of_bellmanFord_eq_some List.mem_finRange hd.1 1

/-- No walk reaches `3`. -/
example : IsShortestDist g 0 3 ⊤ := by
  obtain ⟨d, hd⟩ : ∃ d, bellmanFord g (List.finRange 4) 0 = some d ∧ d 3 = ⊤ :=
    ⟨_, rfl, by decide +kernel⟩
  exact hd.2 ▸ isShortestDist_of_bellmanFord_eq_some List.mem_finRange hd.1 3

example : ¬ NegCycleReachable g 0 := fun h =>
  absurd ((bellmanFord_eq_none_iff List.mem_finRange).2 h) (by decide +kernel)

/-- Word-RAM instance for `g` (`n = 4`, `m = 3`, `maxAbsWeight = 5`). -/
abbrev gInst : Instance := ⟨4, g, 0⟩

/-- At 16-bit word width, `program` halts on `gInst` within `64 * 4 * (4 + 3)` instructions and
outputs `[encodeDist 0, encodeDist 2, encodeDist 5, encodeDist ⊤] = [0, 4, 10, 1]`. -/
example : ∃ steps ≤ 64 * 4 * (4 + 3),
    ExecutesList 16 program (State.init gInst.encode) [0, 4, 10, 1] steps := by
  have hfit : Fits 16 gInst.wordBound := by decide +kernel
  have hm : gInst.m = 3 := by decide +kernel
  have hans : answerWords gInst = [0, 4, 10, 1] := by decide +kernel
  simpa only [hm, hans] using program_spec gInst hfit

-- Executed run of `solver` on `gInst` via the fast compiled interpreter.
/-- info: some ([0, 4, 10, 1], true) -/
#guard_msgs in
#eval runSolver gInst 16

example : (decodeAnswer gInst [0, 4, 10, 1]).map (fun d => (d 0, d 1, d 2, d 3)) =
    some (0, 2, 5, ⊤) := by decide +kernel

/-! ### Parallel edges -/

/-- Parallel edges `0 → 1` of weights `5` and `-3`: the lighter edge `-3` (`Signed.encode (-3) = 7`)
determines the shortest walk. -/
def par : Fin 2 → List (Fin 2 × ℤ)
  | 0 => [(1, 5), (1, -3)]
  | _ => []

abbrev parInst : Instance := ⟨2, par, 0⟩

example : ∃ steps ≤ 64 * 2 * (2 + 2),
    ExecutesList 16 program (State.init parInst.encode) [0, 7] steps := by
  have hfit : Fits 16 parInst.wordBound := by decide +kernel
  have hm : parInst.m = 2 := by decide +kernel
  have hans : answerWords parInst = [0, 7] := by decide +kernel
  simpa only [hm, hans] using program_spec parInst hfit

/-- info: some ([0, 7], true) -/
#guard_msgs in
#eval runSolver parInst 16

example : (decodeAnswer parInst [0, 7]).map (fun d => (d 0, d 1)) =
    some (0, -3) := by decide +kernel

/-! ### Negative cycles -/

/-- `0 → 1` (`1`), `1 → 2` (`-2`), `2 → 1` (`1`): the cycle `1 → 2 → 1` has weight `-1`. -/
def h : Fin 3 → List (Fin 3 × ℤ)
  | 0 => [(1, 1)]
  | 1 => [(2, -2)]
  | 2 => [(1, 1)]

example : bellmanFord h (List.finRange 3) 0 = none := by decide +kernel

example : NegCycleReachable h 0 :=
  (bellmanFord_eq_none_iff List.mem_finRange).1 (by decide +kernel)

/-- The same negative cycle, now unreachable from `0`: `0` has no outgoing edge, and its only edge
comes from the cycle. -/
def h' : Fin 3 → List (Fin 3 × ℤ)
  | 1 => [(2, -2), (0, 0)]
  | 2 => [(1, 1)]
  | _ => []

example : (bellmanFord h' (List.finRange 3) 0).map (fun d => (d 0, d 1, d 2)) =
    some (0, ⊤, ⊤) := by decide +kernel

example : ¬ NegCycleReachable h' 0 := fun hn =>
  absurd ((bellmanFord_eq_none_iff List.mem_finRange).2 hn) (by decide +kernel)

/-- A negative self-loop at the source. -/
example : NegCycleReachable (fun _ : Fin 1 => [((0 : Fin 1), (-1 : ℤ))]) 0 :=
  (bellmanFord_eq_none_iff List.mem_finRange).1 (by decide +kernel)

/-- Word-RAM execution on the reachable negative cycle `h` returns `[]`. -/
abbrev hInst : Instance := ⟨3, h, 0⟩

example : ∃ steps ≤ 64 * 3 * (3 + 3),
    ExecutesList 16 program (State.init hInst.encode) [] steps := by
  have hfit : Fits 16 hInst.wordBound := by decide +kernel
  have hm : hInst.m = 3 := by decide +kernel
  have hans : answerWords hInst = [] := by decide +kernel
  simpa only [hm, hans] using program_spec hInst hfit

/-- info: some ([], true) -/
#guard_msgs in
#eval runSolver hInst 16

/-- Word-RAM execution on the unreachable negative cycle `h'` returns `[0, 1, 1]`
(`(0, ⊤, ⊤)`). -/
abbrev h'Inst : Instance := ⟨3, h', 0⟩

example : ∃ steps ≤ 64 * 3 * (3 + 3),
    ExecutesList 16 program (State.init h'Inst.encode) [0, 1, 1] steps := by
  have hfit : Fits 16 h'Inst.wordBound := by decide +kernel
  have hm : h'Inst.m = 3 := by decide +kernel
  have hans : answerWords h'Inst = [0, 1, 1] := by decide +kernel
  simpa only [hm, hans] using program_spec h'Inst hfit

/-- info: some ([0, 1, 1], true) -/
#guard_msgs in
#eval runSolver h'Inst 16

/-- Word-RAM execution on a negative self-loop at the source returns `[]`. -/
abbrev selfLoopInst : Instance := ⟨1, fun _ => [(0, -1)], 0⟩

example : ∃ steps ≤ 64 * 1 * (1 + 1),
    ExecutesList 16 program (State.init selfLoopInst.encode) [] steps := by
  have hfit : Fits 16 selfLoopInst.wordBound := by decide +kernel
  have hm : selfLoopInst.m = 1 := by decide +kernel
  have hans : answerWords selfLoopInst = [] := by decide +kernel
  simpa only [hm, hans] using program_spec selfLoopInst hfit

/-- info: some ([], true) -/
#guard_msgs in
#eval runSolver selfLoopInst 16

end CslibFrontierTests.BellmanFord
