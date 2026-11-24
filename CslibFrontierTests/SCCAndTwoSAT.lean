/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.Lean.DFS.SCC
public import CslibFrontier.Algorithms.Lean.TwoSAT
public import CslibFrontier.Algorithms.WordRAM.DFS
public meta import CslibFrontier.Algorithms.WordRAM.DFS
public import CslibFrontier.Algorithms.WordRAM.TwoSAT
public meta import CslibFrontier.Algorithms.WordRAM.TwoSAT
meta import CslibFrontier.Computability.WordRAM.Structured.FastEval
public import CslibFrontier.Computability.Complexity.Problems.TwoSAT.PolyTime
public import CslibFrontier.Computability.Complexity.Problems.HornSAT

/-!
# Strongly connected components, linear-time 2-SAT, and polynomial-time 2-SAT/HornSAT tests

Kernel-checked examples (zero `native_decide`) exercising:
1. Kosaraju's strongly connected components (`Cslib.Algorithms.Lean.DFS.sccs`,
   `indexComponents`, `IsSCCCondensation`) on DAGs, cycles, and multi-component graphs, and the
   standard-basis word-RAM component indexing `Cslib.Algorithms.WordRAM.DFS.sccProgram`;
2. Aspvall–Plass–Tarjan linear-time 2-SAT (`Cslib.Algorithms.Lean.TwoSAT` and standard-basis
   Word-RAM `Cslib.Algorithms.WordRAM.TwoSAT`);
3. Native multi-tape Turing-machine polynomial-time `TwoSAT` decision and witness construction
   (`Cslib.Complexity.TwoSAT.solve`, `TwoSAT.assignment`, `TwoSAT.mem_P`), including sparse binary
   variable names;
4. HornSAT least-model minimality (`HornSAT.isLeast_assignment`) and non-uniqueness
   (`HornSAT.exists_multiple_models`).
-/

public section

namespace CslibFrontierTests.SCCAndTwoSAT

open Cslib.Algorithms.Lean.DFS
open Cslib.Logic.PL
open Cslib.Complexity
open Cslib.WordRAM

/-! ### 1. Kosaraju strongly connected components -/

/-- Diamond DAG `0 → 1, 0 → 2, 1 → 3, 2 → 3`: four singleton SCCs. -/
def diamond : Fin 4 → List (Fin 4)
  | 0 => [1, 2]
  | 1 => [3]
  | 2 => [3]
  | 3 => []

example : sccs diamond (List.finRange 4) = [[0], [2], [1], [3]] := by decide +kernel

/-- Triangle `0 → 1 → 2 → 0`: one SCC of size `3`. -/
def triangle : Fin 3 → List (Fin 3)
  | 0 => [1]
  | 1 => [2]
  | 2 => [0]

example : (sccs triangle (List.finRange 3)).length = 1 := by decide +kernel

example :
    let idx := indexComponents (sccs triangle (List.finRange 3))
    idx 0 = 0 ∧ idx 1 = 0 ∧ idx 2 = 0 := by decide +kernel

/-- Two 2-cycles joined by a bridge `0 ↔ 1 → 2 ↔ 3`: `4` vertices and `5` edges. -/
def twoCycles : Fin 4 → List (Fin 4)
  | 0 => [1]
  | 1 => [0, 2]
  | 2 => [3]
  | 3 => [2]

example : (sccs twoCycles (List.finRange 4)).length = 2 := by decide +kernel

example :
    let comps := sccs twoCycles (List.finRange 4)
    let idx := indexComponents comps
    idx 0 = 0 ∧ idx 1 = 0 ∧ idx 2 = 1 ∧ idx 3 = 1 := by
  decide +kernel

example : IsSCCCondensation twoCycles (sccs twoCycles (List.finRange 4)) :=
  isSCCCondensation_sccs List.mem_finRange

private meta def runSCC (G : Cslib.Algorithms.WordRAM.DFS.Graph) (w : ℕ) :
    Option (List ℕ × Bool) :=
  (Cslib.Algorithms.WordRAM.DFS.sccCode.eval w w (Data.init G.encodeCSR)).map fun (y, t) =>
    (outputList y.mem (y.regs Cslib.Algorithms.WordRAM.DFS.Reg.outReg),
      decide (t < 256 * (G.n + G.m + 1)))

/-- Word-RAM component indices agree with `indexComponents ∘ sccs` on the diamond, the triangle,
the bridged 2-cycles, `n = 1` with and without a self-loop, parallel arcs, a disconnected multi-SCC
graph with cross/forward edges, and the empty graph, including tight word-width witnesses. -/
abbrev twoCyclesG : Cslib.Algorithms.WordRAM.DFS.Graph := ⟨4, twoCycles⟩
abbrev emptySCCG : Cslib.Algorithms.WordRAM.DFS.Graph := ⟨0, fun v => v.elim0⟩
abbrev oneNoLoopG : Cslib.Algorithms.WordRAM.DFS.Graph := ⟨1, fun _ => []⟩
abbrev oneSelfLoopG : Cslib.Algorithms.WordRAM.DFS.Graph := ⟨1, fun _ => [0]⟩
abbrev parallelSCCG : Cslib.Algorithms.WordRAM.DFS.Graph :=
  ⟨3, fun | 0 => [1, 1] | 1 => [0, 0] | 2 => [1, 1]⟩

def multiSCC : Fin 6 → List (Fin 6)
  | 0 => [1, 3, 4]
  | 1 => [0, 2]
  | 2 => [3]
  | 3 => [3]
  | 4 => []
  | 5 => []

abbrev multiSCCG : Cslib.Algorithms.WordRAM.DFS.Graph := ⟨6, multiSCC⟩

example : ∃ n, ExecutesList 16 Cslib.Algorithms.WordRAM.DFS.sccProgram
    (State.init twoCyclesG.encodeCSR) [0, 0, 1, 1] n ∧ n ≤ 256 * (4 + 5 + 1) := by
  have h := Cslib.Algorithms.WordRAM.DFS.computesListInTime_sccProgram twoCyclesG 16
    (by decide +kernel) (twoCyclesG.inputFits_encodeCSR (by decide +kernel))
  have hw : Cslib.Algorithms.WordRAM.DFS.sccWords twoCyclesG = [0, 0, 1, 1] := by decide +kernel
  have hm : twoCyclesG.m = 5 := by decide +kernel
  dsimp only at h
  rwa [hw, hm] at h

/-- Tight word-width witness (`w = 5`, `wordBound = 16 < 2 ^ 5`) on the empty graph. -/
example : ∃ n, ExecutesList 5 Cslib.Algorithms.WordRAM.DFS.sccProgram
    (State.init emptySCCG.encodeCSR) [] n ∧ n ≤ 256 := by
  have h := Cslib.Algorithms.WordRAM.DFS.computesListInTime_sccProgram emptySCCG 5
    (by decide +kernel) (emptySCCG.inputFits_encodeCSR (by decide +kernel))
  have hw : Cslib.Algorithms.WordRAM.DFS.sccWords emptySCCG = [] := by decide +kernel
  have hm : emptySCCG.m = 0 := by decide +kernel
  dsimp only at h
  rwa [hw, hm] at h

/-- Tight word-width witness (`w = 8`, `wordBound = 160 < 2 ^ 8`) on `twoCyclesG`. -/
example : ∃ n, ExecutesList 8 Cslib.Algorithms.WordRAM.DFS.sccProgram
    (State.init twoCyclesG.encodeCSR) [0, 0, 1, 1] n ∧ n ≤ 256 * (4 + 5 + 1) := by
  have h := Cslib.Algorithms.WordRAM.DFS.computesListInTime_sccProgram twoCyclesG 8
    (by decide +kernel) (twoCyclesG.inputFits_encodeCSR (by decide +kernel))
  have hw : Cslib.Algorithms.WordRAM.DFS.sccWords twoCyclesG = [0, 0, 1, 1] := by decide +kernel
  have hm : twoCyclesG.m = 5 := by decide +kernel
  dsimp only at h
  rwa [hw, hm] at h

/-- `n = 1` without and with a self-loop on `sccProgram`. -/
example : ∃ n, ExecutesList 16 Cslib.Algorithms.WordRAM.DFS.sccProgram
    (State.init oneNoLoopG.encodeCSR) [0] n ∧ n ≤ 256 * (1 + 0 + 1) := by
  have h := Cslib.Algorithms.WordRAM.DFS.computesListInTime_sccProgram oneNoLoopG 16
    (by decide +kernel) (oneNoLoopG.inputFits_encodeCSR (by decide +kernel))
  have hw : Cslib.Algorithms.WordRAM.DFS.sccWords oneNoLoopG = [0] := by decide +kernel
  have hm : oneNoLoopG.m = 0 := by decide +kernel
  dsimp only at h
  rwa [hw, hm] at h

example : ∃ n, ExecutesList 16 Cslib.Algorithms.WordRAM.DFS.sccProgram
    (State.init oneSelfLoopG.encodeCSR) [0] n ∧ n ≤ 256 * (1 + 1 + 1) := by
  have h := Cslib.Algorithms.WordRAM.DFS.computesListInTime_sccProgram oneSelfLoopG 16
    (by decide +kernel) (oneSelfLoopG.inputFits_encodeCSR (by decide +kernel))
  have hw : Cslib.Algorithms.WordRAM.DFS.sccWords oneSelfLoopG = [0] := by decide +kernel
  have hm : oneSelfLoopG.m = 1 := by decide +kernel
  dsimp only at h
  rwa [hw, hm] at h

/-- Parallel arcs (`transposeCSRCode` repeated cursor decrements) on `sccProgram`. -/
example : ∃ n, ExecutesList 16 Cslib.Algorithms.WordRAM.DFS.sccProgram
    (State.init parallelSCCG.encodeCSR) [1, 1, 0] n ∧ n ≤ 256 * (3 + 6 + 1) := by
  have h := Cslib.Algorithms.WordRAM.DFS.computesListInTime_sccProgram parallelSCCG 16
    (by decide +kernel) (parallelSCCG.inputFits_encodeCSR (by decide +kernel))
  have hw : Cslib.Algorithms.WordRAM.DFS.sccWords parallelSCCG = [1, 1, 0] := by decide +kernel
  have hm : parallelSCCG.m = 6 := by decide +kernel
  dsimp only at h
  rwa [hw, hm] at h

/-- Disconnected / multi-SCC graph with cross and forward edges on `sccProgram`. -/
example : ∃ n, ExecutesList 16 Cslib.Algorithms.WordRAM.DFS.sccProgram
    (State.init multiSCCG.encodeCSR) [1, 1, 3, 4, 2, 0] n ∧ n ≤ 256 * (6 + 7 + 1) := by
  have h := Cslib.Algorithms.WordRAM.DFS.computesListInTime_sccProgram multiSCCG 16
    (by decide +kernel) (multiSCCG.inputFits_encodeCSR (by decide +kernel))
  have hw : Cslib.Algorithms.WordRAM.DFS.sccWords multiSCCG = [1, 1, 3, 4, 2, 0] := by
    decide +kernel
  have hm : multiSCCG.m = 7 := by decide +kernel
  dsimp only at h
  rwa [hw, hm] at h

/-- info: (some ([0, 2, 1, 3], true), some ([0, 0, 0], true)) -/
#guard_msgs in
#eval (runSCC ⟨4, diamond⟩ 16, runSCC ⟨3, triangle⟩ 16)

/-- info: (some ([0, 0, 1, 1], true), some ([], true)) -/
#guard_msgs in
#eval (runSCC twoCyclesG 16, runSCC emptySCCG 5)

/-- info: (some ([0], true), some ([0], true), some ([1, 1, 0], true), some ([1, 1, 3, 4, 2, 0], true)) -/
#guard_msgs in
#eval (runSCC oneNoLoopG 16, runSCC oneSelfLoopG 16, runSCC parallelSCCG 16, runSCC multiSCCG 16)

/-! ### 2. Linear-time 2-SAT solver (pure & standard-basis Word-RAM) -/

private meta def runTwoSAT (G : Cslib.Algorithms.WordRAM.TwoSAT.Instance) (w : ℕ) :
    Option (List ℕ × Bool) :=
  (Cslib.Algorithms.WordRAM.TwoSAT.solver.eval w w (Data.init G.encode)).map fun (y, t) =>
    (outputList y.mem G.outAddrBase, decide (t < 512 * (G.n + G.φ.length + 1)))

/-- `(x₀ ∨ x₁) ∧ (¬x₀ ∨ x₂) ∧ (¬x₁ ∨ x₂)` forces `x₂ = true`. -/
def satFin : CNF (Fin 3) :=
  [[(0, true), (1, true)], [(0, false), (2, true)], [(1, false), (2, true)]]

example :
    ((Cslib.Algorithms.Lean.TwoSAT.solveFin 3 satFin).any fun σ =>
      satFin.eval σ && σ 2) = true := by decide +kernel

abbrev satInst : Cslib.Algorithms.WordRAM.TwoSAT.Instance := ⟨3, satFin⟩

example : InputFits 16 satInst.encode := satInst.inputFits_encode (by decide +kernel)

example : ∃ steps ≤ 512 * (3 + 3 + 1),
    ExecutesList 16 Cslib.Algorithms.WordRAM.TwoSAT.program (State.init satInst.encode)
      (Cslib.Algorithms.WordRAM.TwoSAT.answerWords satInst) steps :=
  Cslib.Algorithms.WordRAM.TwoSAT.program_spec satInst (by decide +kernel)

/-- info: some ([1, 0, 1, 1], true) -/
#guard_msgs in
#eval runTwoSAT satInst 16

/-- Unsatisfiable `CNF (Fin 2)` instance returns `[]`. -/
abbrev unsatFinInst : Cslib.Algorithms.WordRAM.TwoSAT.Instance :=
  ⟨2, [[(0, true), (1, true)], [(0, true), (1, false)],
       [(0, false), (1, true)], [(0, false), (1, false)]]⟩

example : ∃ steps ≤ 512 * (2 + 4 + 1),
    ExecutesList 16 Cslib.Algorithms.WordRAM.TwoSAT.program (State.init unsatFinInst.encode)
      [] steps := by
  have hans : Cslib.Algorithms.WordRAM.TwoSAT.answerWords unsatFinInst = [] := by decide +kernel
  have h := Cslib.Algorithms.WordRAM.TwoSAT.program_spec unsatFinInst (w := 16) (by decide +kernel)
  rwa [hans] at h

/-- info: some ([], true) -/
#guard_msgs in
#eval runTwoSAT unsatFinInst 16

/-- `n = 0` with empty formula `[]` returns `[1]` (satisfied by `Fin.elim0`), whereas `n = 0` with
an empty clause `[[]]` returns `[]`. -/
abbrev emptyFin0Inst : Cslib.Algorithms.WordRAM.TwoSAT.Instance := ⟨0, []⟩
abbrev emptyClauseFin0Inst : Cslib.Algorithms.WordRAM.TwoSAT.Instance := ⟨0, [[]]⟩
abbrev threeLitFinInst : Cslib.Algorithms.WordRAM.TwoSAT.Instance :=
  ⟨3, [[(0, true), (1, true), (2, true)]]⟩

/-- info: (some ([1], true), some ([], true), some ([], true)) -/
#guard_msgs in
#eval (runTwoSAT emptyFin0Inst 16, runTwoSAT emptyClauseFin0Inst 16, runTwoSAT threeLitFinInst 16)

/-- Model boundaries of the implication graph: a unit clause `x₀` with `¬x₀ ∨ x₁` (unit arc
`¬x₀ → x₀`), repeated-literal clauses `x₀ ∨ x₀` and `¬x₀ ∨ ¬x₀` (doubled self-implication arcs),
a tautology `x₀ ∨ ¬x₀` (self-loop arcs `¬x₀ → ¬x₀` and `x₀ → x₀`), and contradictory unit
clauses. -/
abbrev unitInst : Cslib.Algorithms.WordRAM.TwoSAT.Instance :=
  ⟨2, [[(0, true)], [(0, false), (1, true)]]⟩
abbrev dupPosInst : Cslib.Algorithms.WordRAM.TwoSAT.Instance := ⟨1, [[(0, true), (0, true)]]⟩
abbrev dupNegInst : Cslib.Algorithms.WordRAM.TwoSAT.Instance := ⟨1, [[(0, false), (0, false)]]⟩
abbrev tautInst : Cslib.Algorithms.WordRAM.TwoSAT.Instance := ⟨1, [[(0, true), (0, false)]]⟩
abbrev unitClashInst : Cslib.Algorithms.WordRAM.TwoSAT.Instance :=
  ⟨1, [[(0, true)], [(0, false)]]⟩

example : Cslib.Algorithms.WordRAM.TwoSAT.answerWords unitInst = [1, 1, 1] := by decide +kernel

example : Cslib.Algorithms.WordRAM.TwoSAT.answerWords dupPosInst = [1, 1] ∧
    Cslib.Algorithms.WordRAM.TwoSAT.answerWords dupNegInst = [1, 0] ∧
    Cslib.Algorithms.WordRAM.TwoSAT.answerWords unitClashInst = [] := by decide +kernel

/-- info: (some ([1, 1, 1], true), some ([1, 1], true), some ([1, 0], true)) -/
#guard_msgs in
#eval (runTwoSAT unitInst 16, runTwoSAT dupPosInst 16, runTwoSAT dupNegInst 16)

/-- info: (some ([1, 0], true), some ([], true)) -/
#guard_msgs in
#eval (runTwoSAT tautInst 16, runTwoSAT unitClashInst 16)

/-- Symmetry-breaking `x₀ ↔ ¬x₁`: two incomparable literal SCCs. -/
def xorTwo : CNF ℕ :=
  [[(0, true), (1, true)], [(0, false), (1, false)]]

example :
    ((Cslib.Algorithms.Lean.TwoSAT.solveNat xorTwo).any fun σ =>
      xorTwo.eval σ && (σ 0 == !σ 1)) = true := by decide +kernel

/-- Unsatisfiable four-clause 2-CNF `(x₀ ∨ x₁) ∧ (x₀ ∨ ¬x₁) ∧ (¬x₀ ∨ x₁) ∧ (¬x₀ ∨ ¬x₁)`. -/
def unsatTwo : CNF ℕ :=
  [[(0, true), (1, true)], [(0, true), (1, false)],
   [(0, false), (1, true)], [(0, false), (1, false)]]

example : Cslib.Algorithms.Lean.TwoSAT.solveNat unsatTwo = none := by decide +kernel

example : (Cslib.Algorithms.Lean.TwoSAT.solveNat ([] : CNF ℕ)).isSome = true := by decide +kernel

example : Cslib.Algorithms.Lean.TwoSAT.solveNat ([[]] : CNF ℕ) = none := by decide +kernel

example :
    Cslib.Algorithms.Lean.TwoSAT.solveNat ([[(0, true), (1, true), (2, true)]] : CNF ℕ) = none := by
  decide +kernel

/-! ### 3. Multi-tape polynomial-time `TwoSAT` decision and witness construction -/

example : TwoSAT ∈ P encCNF := TwoSAT.mem_P

example : TwoSAT.solve ([] : CNF ℕ) = true := by decide

example : TwoSAT.solve ([[]] : CNF ℕ) = false := by decide

example : TwoSAT.solve ([[(0, true), (1, true), (2, true)]] : CNF ℕ) = false := by decide

example : TwoSAT.solve xorTwo = true ∧ xorTwo.eval (TwoSAT.assignment xorTwo) = true := by decide

example : TwoSAT.solve unsatTwo = false := by decide

/-- Sparse binary variable names (`2 ^ 100` and `7`) require only occurrence-bounded passes. -/
def sparseSat : CNF ℕ :=
  [[(2 ^ 100, true), (7, false)], [(2 ^ 100, false)]]

example :
    TwoSAT.solve sparseSat = true ∧
      sparseSat.eval (TwoSAT.assignment sparseSat) = true ∧
      TwoSAT.assignment sparseSat (2 ^ 100) = false ∧
      TwoSAT.assignment sparseSat 7 = false := by decide

/-! ### 4. HornSAT least model and non-uniqueness -/

theorem horn_implication_least :
    let φ : CNF ℕ := [[(0, false), (1, true)]]
    IsLeast {σ : ℕ → Bool | φ.eval σ = true} (HornSAT.assignment φ) := by
  intro φ
  have hsat : φ ∈ HornSAT := (HornSAT.solve_eq_true_iff φ).mp (by decide)
  exact HornSAT.isLeast_assignment hsat.1 hsat.2

example :
    ∃ (φ : CNF ℕ) (σ : ℕ → Bool),
      φ ∈ HornSAT ∧ φ.eval σ = true ∧ ∃ v ∈ φ.vars, σ v ≠ HornSAT.assignment φ v :=
  HornSAT.exists_multiple_models

end CslibFrontierTests.SCCAndTwoSAT
