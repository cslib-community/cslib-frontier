/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.Hungarian
public import CslibFrontier.Computability.WordRAM.ListOutput
public import CslibFrontier.Computability.WordRAM.Signed.Encoding
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.InputArray
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Foundations.Data.Matrix.PairChunks
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# The Hungarian method in `O(n³)` time on the word RAM

This file implements and proves the `O(n³)` slack-array Kuhn–Munkres (Hungarian) algorithm on the
standard-basis word RAM (`Basis.standard`), connecting its output directly to the pure
specification `Cslib.Algorithms.Lean.MaxFlow.hungarian` and Egerváry's optimality theorem
(`IsMinCostPerfectMatching`).

Two layers are provided:

1. **In-memory nonnegative/shifted cost matrices (`coreCode`, `core_exec`).** Given an `n × n`
   matrix `C : Fin n × Fin n → ℕ` of unsigned costs bounded by `W` stored row-major at `baseC`,
   `coreCode` executes row reduction followed by `n` alternating-tree phases with per-column slacks
   `minv` and predecessor rows `bestRow` in `O(n³)` instructions at every word width satisfying
   `Fits w (baseC + n * n + 8 * n + 2 * W + 2)`. By `HgOuterBound` and `HgStepInv`, all row
   potentials remain in `[0, W]`, negated column potentials remain in `[0, W]`, and reduced costs
   and slacks remain in `[0, 2 * W]`, so unsigned word arithmetic never underflows or overflows.
2. **Signed integer assignment instances from `State.init` (`inputCode`, `assignmentProgram`,
   `minCostProgram`).** An `Instance` specifies `n` and `cost : Fin n × Fin n → ℤ`, encoded as
   `n` followed by the `n²` row-major `Signed.encode` words. `inputCode` scans the input for a
   magnitude bound `M ≤ inst.maxMag`, shifts every cost by `+ M` into `[0, 2 * M]` (preserving
   optimal matchings and dual slack steps by `hungarian_add_const`), runs `coreCode`, writes the
   length-prefixed optimal row-to-column assignment list `inst.assignment` for `ExecutesList` /
   `Program.ComputesListInTime`, and computes `Signed.encode` of the minimum matching cost for
   `Executes` / `Program.ComputesInTime`, all within `hungarianTime inst.n` (`O(n³)`) instructions.

## Main definitions

* `Cslib.Algorithms.WordRAM.Hungarian.Instance`: an `n × n` integer assignment instance.
* `Cslib.Algorithms.WordRAM.Hungarian.Instance.encode`,
  `Cslib.Algorithms.WordRAM.Hungarian.Instance.maxMag`,
  `Cslib.Algorithms.WordRAM.Hungarian.Instance.wordBound`,
  `Cslib.Algorithms.WordRAM.Hungarian.Instance.assignedCol`,
  `Cslib.Algorithms.WordRAM.Hungarian.Instance.assignment`,
  `Cslib.Algorithms.WordRAM.Hungarian.Instance.encodedMinCost`: input encoding, word-width
  envelope, and canonical optimal assignment and minimum-cost outputs.
* `Cslib.Algorithms.WordRAM.Hungarian.BaseRegs`,
  `Cslib.Algorithms.WordRAM.Hungarian.CostMem`: register frame and row-major cost-matrix assertion
  for in-memory calls to `coreCode`.
* `Cslib.Algorithms.WordRAM.Hungarian.coreCode`, `Cslib.Algorithms.WordRAM.Hungarian.inputCode`,
  `Cslib.Algorithms.WordRAM.Hungarian.assignmentProgram`,
  `Cslib.Algorithms.WordRAM.Hungarian.minCostProgram`: structured and flat word-RAM programs.
* `Cslib.Algorithms.WordRAM.Hungarian.coreTime`,
  `Cslib.Algorithms.WordRAM.Hungarian.hungarianTime`: explicit `O(n³)` instruction bounds.

## Main results

* `Cslib.Algorithms.WordRAM.Hungarian.Instance.isMinCostPerfectMatching_assignment`: the pairs
  `(u, inst.assignedCol u)` form `(hungarian inst.cost).matching`, hence a minimum-cost perfect
  matching.
* `Cslib.Algorithms.WordRAM.Hungarian.core_exec`: `O(n³)` word-RAM execution of `coreCode` on an
  in-memory `n × n` unsigned cost matrix `C` bounded by `W`.
* `Cslib.Algorithms.WordRAM.Hungarian.executesList_assignment`,
  `Cslib.Algorithms.WordRAM.Hungarian.computesListInTime_assignment`: `assignmentProgram` computes
  the optimal assignment list in `hungarianTime n = O(n³)` instructions.
* `Cslib.Algorithms.WordRAM.Hungarian.executes_minCost`,
  `Cslib.Algorithms.WordRAM.Hungarian.computesInTime_minCost`: `minCostProgram` computes the
  signed-encoded minimum matching cost in `hungarianTime n = O(n³)` instructions.

## References

* [H. W. Kuhn, *The Hungarian Method for the Assignment Problem*][Kuhn1955]
* [J. Munkres, *Algorithms for the Assignment and Transportation Problems*][Munkres1957]
* [J. Edmonds and R. M. Karp, *Theoretical Improvements in Algorithmic Efficiency for Network Flow
  Problems*][EdmondsKarp1972]
* [A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*][Schrijver2003]
-/

public section

namespace Cslib.Algorithms.WordRAM.Hungarian

open Cslib.WordRAM
open Cslib.Algorithms.Lean.MaxFlow

/-! ## Problem instances and encodings -/

/-- An instance of the `n × n` balanced bipartite minimum-cost assignment problem with integer edge
costs. -/
structure Instance where
  /-- Common side size `n` of the balanced bipartite graph `Fin n × Fin n`. -/
  n : ℕ
  /-- Signed integer cost of pairing row `u` with column `v`. -/
  cost : Fin n × Fin n → ℤ

namespace Instance

/-- Maximum absolute cost `max_{u, v} |cost (u, v)|` (`0` when `n = 0`). -/
@[expose] def maxMag (inst : Instance) : ℕ :=
  Finset.univ.sup fun p : Fin inst.n × Fin inst.n => (inst.cost p).natAbs

theorem natAbs_cost_le_maxMag (inst : Instance) (u v : Fin inst.n) :
    (inst.cost (u, v)).natAbs ≤ inst.maxMag :=
  Finset.le_sup (f := fun p : Fin inst.n × Fin inst.n => (inst.cost p).natAbs)
    (Finset.mem_univ (u, v))

/-- Encode an `n × n` assignment instance as `n` followed by the `n²` row-major `Signed.encode`
cost words. -/
@[expose] def encode (inst : Instance) : List ℕ :=
  inst.n :: (List.finRange inst.n).flatMap fun u =>
    (List.finRange inst.n).map fun v => Signed.encode (inst.cost (u, v))

/-- Sufficient word-value envelope covering all input words, array addresses, shifted potentials,
slacks, and accumulated matching costs. -/
@[expose] def wordBound (inst : Instance) : ℕ :=
  2 * inst.n * inst.n + 8 * inst.n + 4 * (inst.n + 1) * inst.maxMag + 4

/-- Column matched to row `u` in `(hungarian inst.cost).matching`. -/
@[expose] def assignedCol (inst : Instance) (u : Fin inst.n) : Fin inst.n :=
  match (List.finRange inst.n).find?
      (fun v => decide ((u, v) ∈ (hungarian inst.cost).matching)) with
  | some v => v
  | none => u

/-- Row-indexed list `[col_0, …, col_{n - 1}]` of column indices assigned to rows `0, …, n - 1`. -/
@[expose] def assignment (inst : Instance) : List ℕ :=
  (List.finRange inst.n).map fun u => (inst.assignedCol u).val

/-- Minimum perfect-matching cost of `inst`, encoded as an unsigned word via `Signed.encode`. -/
@[expose] def encodedMinCost (inst : Instance) : ℕ :=
  Signed.encode (matchingCost inst.cost (hungarian inst.cost).matching)

@[simp] theorem length_assignment (inst : Instance) : inst.assignment.length = inst.n := by
  simp [assignment]

theorem getElem_assignment (inst : Instance) (u : Fin inst.n) :
    inst.assignment[u.val]'(by simp [assignment]) = (inst.assignedCol u).val := by
  simp [assignment]

theorem mem_matching_assignedCol (inst : Instance) (u : Fin inst.n) :
    (u, inst.assignedCol u) ∈ (hungarian inst.cost).matching := by
  have hperf := (hungarian_correct inst.cost).1.1
  have hu : u ∈ matchedLeft (hungarian inst.cost).matching := by
    rw [hperf.2.1]
    exact Finset.mem_univ u
  obtain ⟨v₀, hv₀⟩ := mem_matchedLeft.mp hu
  let p : Fin inst.n → Bool := fun v => decide ((u, v) ∈ (hungarian inst.cost).matching)
  change (u, match (List.finRange inst.n).find? p with | some v => v | none => u) ∈ _
  cases hfind : (List.finRange inst.n).find? p with
  | some v =>
    have hv : p v = true := List.find?_some hfind
    exact of_decide_eq_true hv
  | none =>
    have hfalse := (List.find?_eq_none.mp hfind) v₀ (List.mem_finRange v₀)
    exact absurd (decide_eq_true hv₀) hfalse

theorem assignedCol_eq_of_mem (inst : Instance) {u v : Fin inst.n}
    (h : (u, v) ∈ (hungarian inst.cost).matching) : inst.assignedCol u = v :=
  ((hungarian_correct inst.cost).1.1.1).2.1 u (inst.assignedCol u) v
    (inst.mem_matching_assignedCol u) h

/-- The Finset of pairs `(u, inst.assignedCol u)` equals `(hungarian inst.cost).matching`. -/
theorem image_assignedCol_eq_matching (inst : Instance) :
    (Finset.univ.image fun u : Fin inst.n => (u, inst.assignedCol u)) =
      (hungarian inst.cost).matching := by
  ext ⟨u, v⟩
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨u', rfl, rfl⟩
    exact inst.mem_matching_assignedCol u'
  · intro h
    exact ⟨u, rfl, inst.assignedCol_eq_of_mem h⟩

/-- The induced matching of `inst.assignment` is a minimum-cost perfect matching of `inst.cost`. -/
theorem isMinCostPerfectMatching_assignment (inst : Instance) :
    IsMinCostPerfectMatching (fun _ => true) inst.cost
      (Finset.univ.image fun u : Fin inst.n => (u, inst.assignedCol u)) := by
  rw [inst.image_assignedCol_eq_matching]
  exact (hungarian_correct inst.cost).1

/-- Summing `inst.cost (u, inst.assignedCol u)` over all rows equals the minimum matching cost. -/
theorem sum_cost_assignedCol (inst : Instance) :
    (∑ u : Fin inst.n, inst.cost (u, inst.assignedCol u)) =
      matchingCost inst.cost (hungarian inst.cost).matching := by
  rw [matchingCost, ← inst.image_assignedCol_eq_matching, Finset.sum_image]
  intro u₁ _ u₂ _ h
  exact (Prod.mk.inj h).1

theorem encode_length (inst : Instance) : inst.encode.length = 1 + inst.n * inst.n := by
  simp [encode, List.length_flatMap, Nat.add_comm]

theorem init_mem_n {r : ℕ} (inst : Instance) :
    (Data.init inst.encode : Data r).mem 1 = inst.n := rfl

theorem init_mem_cost {r : ℕ} (inst : Instance) (u v : Fin inst.n) :
    (Data.init inst.encode : Data r).mem (2 + (u.val * inst.n + v.val)) =
      Signed.encode (inst.cost (u, v)) :=
  Data.init_mem_flatMap_finRange [inst.n] (fun u' v' => Signed.encode (inst.cost (u', v'))) u v

/-- Every instance's encoding fits at any word width admitting `inst.wordBound`. -/
theorem inputFits_encode (inst : Instance) {w : ℕ} (hw : Fits w inst.wordBound) :
    InputFits w inst.encode :=
  InputFits.flatMap_finRange [inst.n] (fun u v => Signed.encode (inst.cost (u, v)))
    (hw.of_le (by unfold wordBound; dsimp only [List.length]; nlinarith))
    (by
      simp only [List.mem_singleton]
      rintro _ rfl
      exact hw.of_le (by unfold wordBound; nlinarith))
    (fun u v => hw.of_le ((Signed.encode_le_two_mul_add_one
      (inst.natAbs_cost_le_maxMag u v)).trans (by unfold wordBound; nlinarith)))

end Instance

/-! ## Registers, memory layout, and structured subroutines -/

namespace Reg

/-- Constant `0`. -/
abbrev zero : Fin 28 := ⟨0, by decide⟩
/-- Constant `1`. -/
abbrev one : Fin 28 := ⟨1, by decide⟩
/-- Constant `2`. -/
abbrev two : Fin 28 := ⟨2, by decide⟩
/-- Side size `n`. -/
abbrev rn : Fin 28 := ⟨3, by decide⟩
/-- Matrix entry count `n * n`. -/
abbrev rnn : Fin 28 := ⟨4, by decide⟩
/-- Shift magnitude `M`. -/
abbrev rM : Fin 28 := ⟨5, by decide⟩
/-- Base of `n × n` shifted cost matrix `C`. -/
abbrev baseC : Fin 28 := ⟨6, by decide⟩
/-- Base of row potentials `y` (`n` words). -/
abbrev baseY : Fin 28 := ⟨7, by decide⟩
/-- Base of negated column potentials `-z` (`n` words). -/
abbrev baseNZ : Fin 28 := ⟨8, by decide⟩
/-- Base of column mates `colMate` (`n` words). -/
abbrev baseColMate : Fin 28 := ⟨9, by decide⟩
/-- Base of tree-column flags `used` (`n` words). -/
abbrev baseUsed : Fin 28 := ⟨10, by decide⟩
/-- Base of tree-row flags `tree` (`n` words). -/
abbrev baseTree : Fin 28 := ⟨11, by decide⟩
/-- Base of column slacks `minv` (`n` words). -/
abbrev baseMinv : Fin 28 := ⟨12, by decide⟩
/-- Base of predecessor rows `bestRow` (`n` words). -/
abbrev baseBestRow : Fin 28 := ⟨13, by decide⟩
/-- Output header cell (`1` word), followed immediately by `rowMate`. -/
abbrev outBase : Fin 28 := ⟨14, by decide⟩
/-- Base of row mates `rowMate` (`n` words, at `outBase + 1`). -/
abbrev baseRowMate : Fin 28 := ⟨15, by decide⟩
/-- Current phase root row `r`. -/
private abbrev rr : Fin 28 := ⟨16, by decide⟩
/-- Phase termination flag (`0` while growing the tree, `1` once augmented). -/
private abbrev augmented : Fin 28 := ⟨17, by decide⟩
/-- Chosen minimum-slack unused column `j₁`. -/
private abbrev rj1 : Fin 28 := ⟨18, by decide⟩
/-- Minimum slack `δ = minv[j₁]`. -/
private abbrev rdelta : Fin 28 := ⟨19, by decide⟩
/-- Matched row `i₀ = colMate[j₁]`. -/
private abbrev ri0 : Fin 28 := ⟨20, by decide⟩
/-- Primary loop index. -/
private abbrev idx : Fin 28 := ⟨21, by decide⟩
/-- Secondary loop index / augmenting-path column cursor. -/
private abbrev idx2 : Fin 28 := ⟨22, by decide⟩
/-- Accumulator / encoded minimum cost output register. -/
abbrev acc : Fin 28 := ⟨23, by decide⟩
/-- Scratch address register. -/
private abbrev addr : Fin 28 := ⟨24, by decide⟩
/-- Scratch value register 1. -/
private abbrev val : Fin 28 := ⟨25, by decide⟩
/-- Scratch value register 2. -/
private abbrev val2 : Fin 28 := ⟨26, by decide⟩
/-- Scratch temporary register. -/
private abbrev tmp : Fin 28 := ⟨27, by decide⟩

end Reg

open Reg

/-- Register frame holding constants, problem dimensions, and all contiguous array base addresses
starting at `bC`. -/
structure BaseRegs (n bC M : ℕ) (x : Data 28) : Prop where
  /-- `zero = 0`. -/
  hzero : x.regs zero = 0
  /-- `one = 1`. -/
  hone : x.regs one = 1
  /-- `two = 2`. -/
  htwo : x.regs two = 2
  /-- `rn = n`. -/
  hrn : x.regs rn = n
  /-- `rnn = n * n`. -/
  hrnn : x.regs rnn = n * n
  /-- `rM = M`. -/
  hrM : x.regs rM = M
  /-- `baseC = bC`. -/
  hbaseC : x.regs baseC = bC
  /-- `baseY = bC + n * n`. -/
  hbaseY : x.regs baseY = bC + n * n
  /-- `baseNZ = bC + n * n + n`. -/
  hbaseNZ : x.regs baseNZ = bC + n * n + n
  /-- `baseColMate = bC + n * n + 2 * n`. -/
  hbaseColMate : x.regs baseColMate = bC + n * n + 2 * n
  /-- `baseUsed = bC + n * n + 3 * n`. -/
  hbaseUsed : x.regs baseUsed = bC + n * n + 3 * n
  /-- `baseTree = bC + n * n + 4 * n`. -/
  hbaseTree : x.regs baseTree = bC + n * n + 4 * n
  /-- `baseMinv = bC + n * n + 5 * n`. -/
  hbaseMinv : x.regs baseMinv = bC + n * n + 5 * n
  /-- `baseBestRow = bC + n * n + 6 * n`. -/
  hbaseBestRow : x.regs baseBestRow = bC + n * n + 6 * n
  /-- `outBase = bC + n * n + 7 * n`. -/
  houtBase : x.regs outBase = bC + n * n + 7 * n
  /-- `baseRowMate = bC + n * n + 7 * n + 1`. -/
  hbaseRowMate : x.regs baseRowMate = bC + n * n + 7 * n + 1

private theorem BaseRegs.of_eq {n bC M : ℕ} {x y : Data 28} (h : BaseRegs n bC M x)
    (heq : ∀ i : Fin 28, i.val < 16 → y.regs i = x.regs i) : BaseRegs n bC M y where
  hzero := (heq zero (by decide)).trans h.hzero
  hone := (heq one (by decide)).trans h.hone
  htwo := (heq two (by decide)).trans h.htwo
  hrn := (heq rn (by decide)).trans h.hrn
  hrnn := (heq rnn (by decide)).trans h.hrnn
  hrM := (heq rM (by decide)).trans h.hrM
  hbaseC := (heq baseC (by decide)).trans h.hbaseC
  hbaseY := (heq baseY (by decide)).trans h.hbaseY
  hbaseNZ := (heq baseNZ (by decide)).trans h.hbaseNZ
  hbaseColMate := (heq baseColMate (by decide)).trans h.hbaseColMate
  hbaseUsed := (heq baseUsed (by decide)).trans h.hbaseUsed
  hbaseTree := (heq baseTree (by decide)).trans h.hbaseTree
  hbaseMinv := (heq baseMinv (by decide)).trans h.hbaseMinv
  hbaseBestRow := (heq baseBestRow (by decide)).trans h.hbaseBestRow
  houtBase := (heq outBase (by decide)).trans h.houtBase
  hbaseRowMate := (heq baseRowMate (by decide)).trans h.hbaseRowMate

/-- Memory holds the `n × n` unsigned cost matrix `C` row-major at `bC`. -/
@[expose] def CostMem {n : ℕ} (bC : ℕ) (C : Fin n × Fin n → ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ u v : Fin n, mem (bC + (u.val * n + v.val)) = C (u, v)

private theorem CostMem.of_outside {n bC : ℕ} {C : Fin n × Fin n → ℕ} {m₁ m₂ : ℕ → ℕ}
    (h : CostMem bC C m₁) (hout : ∀ a, a < bC + n * n → m₂ a = m₁ a) : CostMem bC C m₂ := by
  intro u v
  have hlt : u.val * n + v.val < n * n := Cslib.Matrix.pairIndex_lt (u, v)
  rw [hout _ (by omega)]
  exact h u v

/-- Encode `Option (Fin n)` as `n` for `none` and `i.val` for `some i`. -/
private def encodeOptFin {n : ℕ} : Option (Fin n) → ℕ
  | none => n
  | some i => i.val

/-- Between-phase memory representation of `(y, z, mate)` at layout `bC`. -/
private structure OuterMem {n : ℕ} (bC : ℕ) (y z : Vector ℤ n) (mate : Vector (Option (Fin n)) n)
    (mem : ℕ → ℕ) : Prop where
  /-- `y` block stores `(vget y i).toNat`. -/
  hy : ∀ i : Fin n, mem (bC + n * n + i.val) = (vget y i).toNat
  /-- `nz` block stores `(-vget z j).toNat`. -/
  hnz : ∀ j : Fin n, mem (bC + n * n + n + j.val) = (-vget z j).toNat
  /-- `colMate` block stores `encodeOptFin (vget mate j)`. -/
  hcol : ∀ j : Fin n, mem (bC + n * n + 2 * n + j.val) = encodeOptFin (vget mate j)
  /-- Matched rows map to their matched column in `rowMate`. -/
  hrow_some : ∀ j i : Fin n, vget mate j = some i →
    mem (bC + n * n + 7 * n + 1 + i.val) = j.val
  /-- Unmatched rows hold sentinel `n` in `rowMate`. -/
  hrow_none : ∀ i : Fin n, (∀ j : Fin n, vget mate j ≠ some i) →
    mem (bC + n * n + 7 * n + 1 + i.val) = n

/-- Within-phase memory representation of `(s, bestRow)` at layout `bC`. -/
private structure StepMem {n : ℕ} (bC : ℕ) (s : HgState n) (bestRow : Fin n → Fin n)
    (mem : ℕ → ℕ) : Prop extends OuterMem bC s.y s.z s.mate mem where
  /-- `used` block stores `0`/`1` flags for `s.used`. -/
  hused : ∀ j : Fin n, mem (bC + n * n + 3 * n + j.val) = if vget s.used j = true then 1 else 0
  /-- `tree` block stores `0`/`1` flags for `s.tree`. -/
  htree : ∀ i : Fin n, mem (bC + n * n + 4 * n + i.val) = if vget s.tree i = true then 1 else 0
  /-- `minv` block stores `(vget s.minv j).toNat`. -/
  hminv : ∀ j : Fin n, mem (bC + n * n + 5 * n + j.val) = (vget s.minv j).toNat
  /-- `bestRow` block stores `(bestRow j).val`. -/
  hbest : ∀ j : Fin n, mem (bC + n * n + 6 * n + j.val) = (bestRow j).val

private theorem hgRed_nat_eq {n W : ℕ} {C : Fin n × Fin n → ℕ} {y z : Vector ℤ n} {i j : Fin n}
    (hCW : C (i, j) ≤ W)
    (hy : 0 ≤ vget y i ∧ vget y i ≤ W)
    (hz : -(W : ℤ) ≤ vget z j ∧ vget z j ≤ 0)
    (hfeas : 0 ≤ hgRed (fun p => (C p : ℤ)) y z i j) :
    (vget y i).toNat ≤ C (i, j) + (-vget z j).toNat ∧
      C (i, j) + (-vget z j).toNat ≤ 2 * W ∧
      C (i, j) + (-vget z j).toNat - (vget y i).toNat =
        (hgRed (fun p => (C p : ℤ)) y z i j).toNat := by
  unfold hgRed at hfeas ⊢
  dsimp only at hfeas ⊢
  omega

private theorem exec_forLoop {w N T : ℕ} {idxReg limReg : Fin 28}
    {body : Code .standard 28} (P : ℕ → Data 28 → Prop)
    (hlim : ∀ y, P (y.regs idxReg) y → y.regs limReg = N)
    (hbody : ∀ y, P (y.regs idxReg) y → y.regs idxReg < N →
      ∃ z, ExecWithin w body y z T ∧ P (y.regs idxReg + 1) z ∧
        z.regs idxReg = y.regs idxReg + 1)
    {x : Data 28} (h0 : P 0 (x.set idxReg 0)) :
    ∃ y, ExecWithin w (.seq (ram[ idxReg ← #0 ]) (.loop (.lt idxReg limReg) body)) x y
      (N * (T + 2) + 3) ∧ P N y := by
  have hs₀ : ExecWithin w (ram[ idxReg ← #0 ] : Code .standard 28) x (x.set idxReg 0) 1 := by
    refine WP.execWithin ?_
    wram_exec
    rfl
  have hidx0 : (x.set idxReg 0).regs idxReg = 0 := Data.set_regs_self x idxReg 0
  have h0' : P ((x.set idxReg 0).regs idxReg) (x.set idxReg 0) := by
    rw [hidx0]
    exact h0
  obtain ⟨y, hl, hPN, _⟩ := ExecWithin.loop_count P hlim hbody
    (by rw [hidx0]; exact Nat.zero_le N) h0'
  refine ⟨y, (hs₀.seq hl).mono ?_, hPN⟩
  rw [hidx0, Nat.sub_zero]
  omega

/-! ### Reusable leaf loops -/

/-- Fill `[dst, dst + n)` with `valReg`. -/
private abbrev fillConst (dst valReg : Fin 28) : Code .standard 28 :=
  Cslib.WordRAM.fillConst dst rn valReg one idx addr

private theorem exec_fillConst {w n bC M : ℕ} (dst valReg : Fin 28)
    (hd_lt : dst.val < 21) (hv_lt : valReg.val < 21) (x : Data 28)
    (hb : BaseRegs n bC M x) (hdst : x.regs dst + n ≤ bC + n * n + 8 * n + 1)
    (hfit : Fits w (bC + n * n + 8 * n + 2)) :
    ∃ y, ExecWithin w (fillConst dst valReg) x y (5 * n + 3) ∧
      (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ k < n, y.mem (x.regs dst + k) = x.regs valReg) ∧
      (∀ a, ¬(x.regs dst ≤ a ∧ a < x.regs dst + n) → y.mem a = x.mem a) := by
  have hne : ∀ j : Fin 28, j.val < 21 → idx ≠ j ∧ addr ≠ j := fun j hj =>
    ⟨fun h => by subst h; simp at hj, fun h => by subst h; simp at hj⟩
  obtain ⟨y, he, hr, _, hmem⟩ := Cslib.WordRAM.fillConst_exec (w := w)
    (base := dst) (len := rn) (val := valReg) (one := one) (idx := idx) (addr := addr)
    (hne dst hd_lt).1 (by decide) (hne valReg hv_lt).1 (by decide)
    (hne dst hd_lt).2 (by decide) (hne valReg hv_lt).2 (by decide) (by decide)
    hb.hone (by rw [hb.hrn]; exact hfit.of_le (by omega))
    (by rw [hb.hrn]; exact hfit.of_le (by omega))
  rw [hb.hrn] at he hmem
  exact ⟨y, he.within, fun i hi => hr i (hne i hi).1.symm (hne i hi).2.symm,
    fun k hk => by rw [hmem]; exact fill_of_owns ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hk _⟩,
    fun a ha => by rw [hmem]; exact fill_of_not_owns ha⟩

/-- Inner loop body scanning row `idx` for its minimum entry. -/
private def rowMinBody : Code .standard 28 := ram[
  addr ← idx * rn; addr ← addr + idx2; addr ← baseC + addr; val ← *addr;
  if val < acc then [ acc ← val ] else [ tmp ← zero ];
  idx2 ← idx2 + one ]

/-- Compute `hgRowMin` of row `idx` into `acc`. -/
private def rowMinCode : Code .standard 28 :=
  .seq (ram[ addr ← idx * rn; addr ← addr + idx; addr ← baseC + addr; acc ← *addr; idx2 ← #0 ])
    (.loop (.lt idx2 rn) rowMinBody)

private theorem exec_rowMinCode {w n bC M W : ℕ} {C : Fin n × Fin n → ℕ}
    (hCW : ∀ u v, C (u, v) ≤ W) (u : Fin n) (x : Data 28)
    (hb : BaseRegs n bC M x) (hC : CostMem bC C x.mem) (hu : x.regs idx = u.val)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y, ExecWithin w rowMinCode x y (10 * n + 7) ∧
      (∀ i : Fin 28, i.val < 22 → y.regs i = x.regs i) ∧
      y.mem = x.mem ∧
      y.regs acc = (hgRowMin (fun p => (C p : ℤ)) u).toNat := by
  let c : Fin n × Fin n → ℤ := fun p => (C p : ℤ)
  let P (k : ℕ) (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 22 → y.regs i = x.regs i) ∧
      y.mem = x.mem ∧
      y.regs acc ≤ W ∧
      (y.regs acc : ℤ) = ((List.finRange n).take k).foldl (fun a v => min a (c (u, v))) (c (u, u))
  have hstepBody (y : Data 28) (hy : P (y.regs idx2) y) (hlt : y.regs idx2 < n) :
      ∃ z, ExecWithin w rowMinBody y z 8 ∧ P (y.regs idx2 + 1) z ∧
        z.regs idx2 = y.regs idx2 + 1 := by
    obtain ⟨hr, hmem, haccW, haccEq⟩ := hy
    let v : Fin n := ⟨y.regs idx2, hlt⟩
    have hidx : y.regs idx = u.val := (hr idx (by decide)).trans hu
    have hrn_y : y.regs rn = n := (hr rn (by decide)).trans hb.hrn
    have hbC_y : y.regs baseC = bC := (hr baseC (by decide)).trans hb.hbaseC
    have hz_y : y.regs zero = 0 := (hr zero (by decide)).trans hb.hzero
    have ho_y : y.regs one = 1 := (hr one (by decide)).trans hb.hone
    have hmul_lt : u.val * n + y.regs idx2 < n * n := Cslib.Matrix.pairIndex_lt (u, v)
    have hf1 : Fits w (u.val * n) := hfit.of_le (by omega)
    have hf2 : Fits w (u.val * n + y.regs idx2) := hfit.of_le (by omega)
    have hf3 : Fits w (bC + (u.val * n + u.val)) :=
      hfit.of_le (by have : u.val * n + u.val < n * n := Cslib.Matrix.pairIndex_lt (u, u); omega)
    have hf3' : Fits w (bC + (u.val * n + y.regs idx2)) := hfit.of_le (by omega)
    have hf4 : Fits w (y.regs idx2 + 1) := hfit.of_le (by omega)
    have hload : y.mem (bC + (u.val * n + y.regs idx2)) = C (u, v) := by
      rw [hmem]
      exact hC u v
    have htk := List.take_succ_finRange hlt
    refine WP.exists_execWithin ?_
    unfold rowMinBody
    by_cases hcmp : C (u, v) < y.regs acc
    · wram_exec [hidx, hrn_y, hbC_y, hz_y, ho_y, hload, hcmp, hf1, hf2, hf3', hf4]
      refine ⟨⟨fun i hi => by wram_simp [hr i hi], hmem, ?_, ?_⟩, by wram_simp⟩
      · wram_simp
        exact hCW u v
      · wram_simp
        rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil, ← haccEq]
        dsimp only [c, v] at hcmp ⊢
        simp only [min_def]
        split_ifs <;> omega
    · wram_exec [hidx, hrn_y, hbC_y, hz_y, ho_y, hload, hcmp, hf1, hf2, hf3', hf4]
      refine ⟨⟨fun i hi => by wram_simp [hr i hi], hmem, ?_, ?_⟩, by wram_simp⟩
      · wram_simp
        exact haccW
      · wram_simp
        rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil, ← haccEq]
        dsimp only [c, v] at hcmp ⊢
        simp only [min_def]
        split_ifs <;> omega
  have hmul_uu : u.val * n + u.val < n * n := Cslib.Matrix.pairIndex_lt (u, u)
  have hf1 : Fits w (u.val * n) := hfit.of_le (by omega)
  have hf2 : Fits w (u.val * n + u.val) := hfit.of_le (by omega)
  have hf3 : Fits w (bC + (u.val * n + u.val)) := hfit.of_le (by omega)
  have hload0 : x.mem (bC + (u.val * n + u.val)) = C (u, u) := hC u u
  have hs₀ : ∃ s₀, ExecWithin w
      (ram[ addr ← idx * rn; addr ← addr + idx; addr ← baseC + addr; acc ← *addr; idx2 ← #0 ] :
        Code .standard 28)
      x s₀ 5 ∧ P 0 s₀ ∧ s₀.regs idx2 = 0 := by
    refine WP.exists_execWithin ?_
    wram_exec [hu, hb.hrn, hb.hbaseC, hload0, hf1, hf2, hf3]
    exact ⟨⟨fun i hi => by wram_simp, rfl, by wram_simp; exact hCW u u,
      by wram_simp; simp [c]⟩, by wram_simp⟩
  obtain ⟨s₀, hes₀, hPs₀, hidxs₀⟩ := hs₀
  obtain ⟨y, hl, hPn, _⟩ := ExecWithin.loop_count P
    (fun y hy => (hy.1 rn (by decide)).trans hb.hrn) hstepBody (by omega) (hidxs₀ ▸ hPs₀)
  obtain ⟨hr, hmem, _, haccEq⟩ := hPn
  refine ⟨y, (hes₀.seq hl).mono (by rw [hidxs₀]; omega), hr, hmem, ?_⟩
  have hfull : (List.finRange n).take n = List.finRange n :=
    List.take_of_length_le (by simp)
  rw [hfull] at haccEq
  change (y.regs acc : ℤ) = hgRowMin c u at haccEq
  have hnonneg := (hgRowMin_bounds (c := c)
    (fun u' v' => ⟨Nat.cast_nonneg _, Nat.cast_le.mpr (hCW u' v')⟩) u).1
  dsimp only [c] at haccEq hnonneg
  omega

/-- Body of `initYCode`: compute row minimum and store it into `y[idx]`. -/
private def initYBody : Code .standard 28 :=
  .seq rowMinCode (ram[ addr ← baseY + idx; *addr ← acc; idx ← idx + one ])

/-- Populate `y[0..n)` with `hgRowMin`. -/
private def initYCode : Code .standard 28 :=
  .seq (ram[ idx ← #0 ]) (.loop (.lt idx rn) initYBody)

private theorem exec_initYCode {w n bC M W : ℕ} {C : Fin n × Fin n → ℕ}
    (hCW : ∀ u v, C (u, v) ≤ W) (x : Data 28)
    (hb : BaseRegs n bC M x) (hC : CostMem bC C x.mem)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y, ExecWithin w initYCode x y (10 * n * n + 12 * n + 3) ∧
      (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ u : Fin n, y.mem (bC + n * n + u.val) = (hgRowMin (fun p => (C p : ℤ)) u).toNat) ∧
      (∀ a, ¬(bC + n * n ≤ a ∧ a < bC + n * n + n) → y.mem a = x.mem a) := by
  let c : Fin n × Fin n → ℤ := fun p => (C p : ℤ)
  let d := bC + n * n
  let e : ℕ → ℕ := fun k => if hk : k < n then (hgRowMin c ⟨k, hk⟩).toNat else 0
  let P (k : ℕ) (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ j < k, y.mem (d + j) = e j) ∧
      (∀ a, ¬(d ≤ a ∧ a < d + k) → y.mem a = x.mem a)
  have hbody (y : Data 28) (hy : P (y.regs idx) y) (hlt : y.regs idx < n) :
      ∃ z, ExecWithin w initYBody y z (10 * n + 10) ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hm, hf⟩ := hy
    let u : Fin n := ⟨y.regs idx, hlt⟩
    have hby : BaseRegs n bC M y := hb.of_eq fun i hi => hr i (by omega)
    have hCy : CostMem bC C y.mem := hC.of_outside fun a ha => hf a (by omega)
    obtain ⟨y₁, he₁, hr₁, hmem₁, hacc₁⟩ := exec_rowMinCode hCW u y hby hCy rfl hfit
    have hbY₁ : y₁.regs baseY = d :=
      ((hr₁ baseY (by decide)).trans (hr baseY (by decide))).trans hb.hbaseY
    have hidx₁ : y₁.regs idx = y.regs idx := hr₁ idx (by decide)
    have hone₁ : y₁.regs one = 1 :=
      ((hr₁ one (by decide)).trans (hr one (by decide))).trans hb.hone
    have hf_addr : Fits w (d + y.regs idx) := hfit.of_le (by omega)
    have hf_next : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    have hej : y₁.regs acc = e (y.regs idx) := by
      simp only [e, hlt, dite_true]
      exact hacc₁
    have hstep₂ : ∃ z, ExecWithin w
        (ram[ addr ← baseY + idx; *addr ← acc; idx ← idx + one ] : Code .standard 28) y₁ z 3 ∧
        z = ((y₁.set addr (d + y.regs idx)).write (d + y.regs idx) (e (y.regs idx))).set idx
          (y.regs idx + 1) := by
      refine WP.exists_execWithin ?_
      wram_exec [hbY₁, hidx₁, hone₁, hej, hf_addr, hf_next]
      rfl
    obtain ⟨z, he₂, rfl⟩ := hstep₂
    have hmem_z : (((y₁.set addr (d + y.regs idx)).write (d + y.regs idx) (e (y.regs idx))).set idx
        (y.regs idx + 1)).mem = Function.update y.mem (d + y.regs idx) (e (y.regs idx)) := by
      rw [← hmem₁]
      rfl
    obtain ⟨hm', hf'⟩ := prefix_write_step hm hf hmem_z
    refine ⟨_, (he₁.seq he₂).mono (by omega), ⟨fun i hi => ?_, hm', hf'⟩, by wram_simp⟩
    wram_simp [hr₁ i (by omega), hr i hi]
  obtain ⟨y, he, hr, hm, hf⟩ := exec_forLoop P
    (fun y hy => (hy.1 rn (by decide)).trans hb.hrn) hbody (x := x)
    ⟨fun i hi => by wram_simp, fun _ hj => by omega, fun _ _ => rfl⟩
  refine ⟨y, he.mono (by nlinarith), hr, fun u => ?_, hf⟩
  simpa [d, e, u.isLt] using hm u.val u.isLt

/-- Initialize `y`, `nz`, `colMate`, and `rowMate` before the first phase. -/
private def initOuterCode : Code .standard 28 :=
  .seq initYCode
    (.seq (fillConst baseNZ zero)
      (.seq (fillConst baseColMate rn) (fillConst baseRowMate rn)))

private theorem exec_initOuterCode {w n bC M W : ℕ} {C : Fin n × Fin n → ℕ}
    (hCW : ∀ u v, C (u, v) ≤ W) (x : Data 28)
    (hb : BaseRegs n bC M x) (hC : CostMem bC C x.mem)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y, ExecWithin w initOuterCode x y (10 * n * n + 27 * n + 12) ∧
      (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      OuterMem bC (Vector.ofFn (hgRowMin fun p => (C p : ℤ))) (Vector.replicate n 0)
        (Vector.replicate n none) y.mem ∧
      (∀ a, ¬(bC + n * n ≤ a ∧ a < bC + n * n + 8 * n + 1 ∧ a ≠ bC + n * n + 7 * n) →
        y.mem a = x.mem a) := by
  have hfit_a : Fits w (bC + n * n + 8 * n + 2) := hfit.of_le (by omega)
  obtain ⟨y₁, he₁, hr₁, hy₁, hf₁⟩ := exec_initYCode hCW x hb hC hfit
  have hb₁ : BaseRegs n bC M y₁ := hb.of_eq fun i hi => hr₁ i (by omega)
  obtain ⟨y₂, he₂, hr₂, hnz₂, hf₂⟩ := exec_fillConst baseNZ zero (by decide) (by decide) y₁ hb₁
    (by rw [hb₁.hbaseNZ]; omega) hfit_a
  have hb₂ : BaseRegs n bC M y₂ := hb₁.of_eq fun i hi => hr₂ i (by omega)
  obtain ⟨y₃, he₃, hr₃, hcm₃, hf₃⟩ := exec_fillConst baseColMate rn (by decide) (by decide) y₂ hb₂
    (by rw [hb₂.hbaseColMate]; omega) hfit_a
  have hb₃ : BaseRegs n bC M y₃ := hb₂.of_eq fun i hi => hr₃ i (by omega)
  obtain ⟨y₄, he₄, hr₄, hrm₄, hf₄⟩ := exec_fillConst baseRowMate rn (by decide) (by decide) y₃ hb₃
    (by rw [hb₃.hbaseRowMate]; omega) hfit_a
  refine ⟨y₄, (he₁.seq (he₂.seq (he₃.seq he₄))).mono (by nlinarith),
    fun i hi => (((hr₄ i hi).trans (hr₃ i hi)).trans (hr₂ i hi)).trans (hr₁ i hi),
    ⟨fun i => ?_, fun j => ?_, fun j => ?_, fun j i hm => ?_, fun i _ => ?_⟩, fun a ha => ?_⟩
  · rw [hf₄ _ (by rw [hb₃.hbaseRowMate]; have := i.isLt; omega),
      hf₃ _ (by rw [hb₂.hbaseColMate]; have := i.isLt; omega),
      hf₂ _ (by rw [hb₁.hbaseNZ]; have := i.isLt; omega), hy₁ i]
    simp [vget]
  · rw [hf₄ _ (by rw [hb₃.hbaseRowMate]; have := j.isLt; omega),
      hf₃ _ (by rw [hb₂.hbaseColMate]; have := j.isLt; omega)]
    have := hnz₂ j.val j.isLt
    rw [hb₁.hbaseNZ, hb₁.hzero] at this
    simpa [vget] using this
  · rw [hf₄ _ (by rw [hb₃.hbaseRowMate]; have := j.isLt; omega)]
    have := hcm₃ j.val j.isLt
    rw [hb₂.hbaseColMate, hb₂.hrn] at this
    simpa [vget, encodeOptFin] using this
  · simp [vget] at hm
  · have := hrm₄ i.val i.isLt
    rwa [hb₃.hbaseRowMate, hb₃.hrn] at this
  · rw [hf₄ a (by rw [hb₃.hbaseRowMate]; omega),
      hf₃ a (by rw [hb₂.hbaseColMate]; omega),
      hf₂ a (by rw [hb₁.hbaseNZ]; omega),
      hf₁ a (by omega)]

/-- Initialize `minv[j] := C[rr, j] + nz[j] - y[rr]` for `j = 0 .. n - 1`. -/
private def initMinvBody : Code .standard 28 := ram[
  addr ← rr * rn; addr ← addr + idx; addr ← baseC + addr; val ← *addr;
  addr ← baseNZ + idx; val2 ← *addr; val ← val + val2;
  addr ← baseY + rr; val2 ← *addr; val ← val - val2;
  addr ← baseMinv + idx; *addr ← val; idx ← idx + one ]

/-- Compute initial column slacks for phase `rr`. -/
private def initMinvCode : Code .standard 28 :=
  .seq (ram[ idx ← #0 ]) (.loop (.lt idx rn) initMinvBody)

private theorem exec_initMinvCode {w n bC M W : ℕ} {C : Fin n × Fin n → ℕ}
    {y₀ z₀ : Vector ℤ n} {mate₀ : Vector (Option (Fin n)) n}
    (hCW : ∀ u v, C (u, v) ≤ W)
    (hOB : HgOuterBound (fun p => (C p : ℤ)) W y₀ z₀ mate₀)
    (r : Fin n) (x : Data 28) (hb : BaseRegs n bC M x)
    (hC : CostMem bC C x.mem) (hOM : OuterMem bC y₀ z₀ mate₀ x.mem)
    (hr_reg : x.regs rr = r.val)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y, ExecWithin w initMinvCode x y (15 * n + 3) ∧
      (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ j : Fin n, y.mem (bC + n * n + 5 * n + j.val) =
        (hgRed (fun p => (C p : ℤ)) y₀ z₀ r j).toNat) ∧
      (∀ a, ¬(bC + n * n + 5 * n ≤ a ∧ a < bC + n * n + 6 * n) → y.mem a = x.mem a) := by
  let c : Fin n × Fin n → ℤ := fun p => (C p : ℤ)
  let d := bC + n * n + 5 * n
  let e : ℕ → ℕ := fun k => if hk : k < n then (hgRed c y₀ z₀ r ⟨k, hk⟩).toNat else 0
  let P (k : ℕ) (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ j < k, y.mem (d + j) = e j) ∧
      (∀ a, ¬(d ≤ a ∧ a < d + k) → y.mem a = x.mem a)
  have hbody (y : Data 28) (hy : P (y.regs idx) y) (hlt : y.regs idx < n) :
      ∃ z, ExecWithin w initMinvBody y z 13 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hm, hf⟩ := hy
    let j : Fin n := ⟨y.regs idx, hlt⟩
    have hby : BaseRegs n bC M y := hb.of_eq fun i hi => hr i (by omega)
    have hrr_y : y.regs rr = r.val := (hr rr (by decide)).trans hr_reg
    have hmul : r.val * n + y.regs idx < n * n := Cslib.Matrix.pairIndex_lt (r, j)
    obtain ⟨hle_sub, hsum_le, hred_eq⟩ := hgRed_nat_eq (hCW r j) (hOB.y_bounds r)
      (hOB.z_bounds j) (hOB.feas r j)
    have hC_rj : y.mem (bC + (r.val * n + y.regs idx)) = C (r, j) := by
      rw [hf _ (by omega)]
      exact hC r j
    have hnz_j : y.mem (bC + n * n + n + y.regs idx) = (-vget z₀ j).toNat := by
      rw [hf _ (by omega)]
      exact hOM.hnz j
    have hy_r : y.mem (bC + n * n + r.val) = (vget y₀ r).toNat := by
      rw [hf _ (by omega)]
      exact hOM.hy r
    have hf1 : Fits w (r.val * n) := hfit.of_le (by omega)
    have hf2 : Fits w (r.val * n + y.regs idx) := hfit.of_le (by omega)
    have hf3 : Fits w (bC + (r.val * n + y.regs idx)) := hfit.of_le (by omega)
    have hf4 : Fits w (bC + n * n + n + y.regs idx) := hfit.of_le (by omega)
    have hf5 : Fits w (C (r, j) + (-vget z₀ j).toNat) := hfit.of_le (by omega)
    have hf6 : Fits w (bC + n * n + r.val) := hfit.of_le (by have := r.isLt; omega)
    have hf7 : Fits w (C (r, j) + (-vget z₀ j).toNat - (vget y₀ r).toNat) := hfit.of_le (by omega)
    have hf8 : Fits w (d + y.regs idx) := hfit.of_le (by omega)
    have hf9 : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    have hej : C (r, j) + (-vget z₀ j).toNat - (vget y₀ r).toNat = e (y.regs idx) := by
      simp only [e, hlt, dite_true]
      exact hred_eq
    have hstep : ∃ z, ExecWithin w initMinvBody y z 13 ∧
        z.mem = Function.update y.mem (d + y.regs idx) (e (y.regs idx)) ∧
        (∀ i : Fin 28, i.val < 21 → z.regs i = x.regs i) ∧
        z.regs idx = y.regs idx + 1 := by
      refine WP.exists_execWithin ?_
      unfold initMinvBody
      wram_exec [hrr_y, hby.hrn, hby.hbaseC, hby.hbaseNZ, hby.hbaseY, hby.hbaseMinv, hby.hone,
        hC_rj, hnz_j, hy_r, hle_sub, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9]
      refine ⟨?_, fun i hi => by wram_simp [hr i hi], by wram_simp⟩
      wram_simp [d, hej]
    obtain ⟨z, he, hmz, hrz, hiz⟩ := hstep
    obtain ⟨hm', hf'⟩ := prefix_write_step hm hf hmz
    exact ⟨z, he, ⟨hrz, hm', hf'⟩, hiz⟩
  obtain ⟨y, he, hr, hm, hf⟩ := exec_forLoop P
    (fun y hy => (hy.1 rn (by decide)).trans hb.hrn) hbody (x := x)
    ⟨fun i hi => by wram_simp, fun _ hj => by omega, fun _ _ => rfl⟩
  refine ⟨y, he.mono (by omega), hr, fun j => ?_, fun a ha => hf a (by simp only [d]; omega)⟩
  simpa [d, e, j.isLt] using hm j.val j.isLt

/-- Initialize all phase arrays (`used`, `tree`, `bestRow`, `minv`, and `augmented = 0`). -/
private def initPhaseCode : Code .standard 28 :=
  .seq (fillConst baseUsed zero)
    (.seq (fillConst baseTree zero)
      (.seq (ram[ addr ← baseTree + rr; *addr ← one ])
        (.seq (fillConst baseBestRow rr)
          (.seq initMinvCode (ram[ augmented ← #0 ])))))

private theorem exec_initPhaseCode {w n bC M W : ℕ} {C : Fin n × Fin n → ℕ}
    {y₀ z₀ : Vector ℤ n} {mate₀ : Vector (Option (Fin n)) n}
    (hCW : ∀ u v, C (u, v) ≤ W)
    (hOB : HgOuterBound (fun p => (C p : ℤ)) W y₀ z₀ mate₀)
    (r : Fin n) (x : Data 28) (hb : BaseRegs n bC M x)
    (hC : CostMem bC C x.mem) (hOM : OuterMem bC y₀ z₀ mate₀ x.mem)
    (hr_reg : x.regs rr = r.val)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y, ExecWithin w initPhaseCode x y (30 * n + 15) ∧
      (∀ i : Fin 28, i.val < 17 → y.regs i = x.regs i) ∧
      y.regs augmented = 0 ∧
      StepMem bC (hgInit (fun p => (C p : ℤ)) y₀ z₀ mate₀ r) (fun _ => r) y.mem ∧
      (∀ a, ¬(bC + n * n + 3 * n ≤ a ∧ a < bC + n * n + 7 * n) → y.mem a = x.mem a) := by
  have hfit_a : Fits w (bC + n * n + 8 * n + 2) := hfit.of_le (by omega)
  obtain ⟨y₁, he₁, hr₁, hused₁, hf₁⟩ := exec_fillConst baseUsed zero (by decide) (by decide) x hb
    (by rw [hb.hbaseUsed]; omega) hfit_a
  have hb₁ : BaseRegs n bC M y₁ := hb.of_eq fun i hi => hr₁ i (by omega)
  obtain ⟨y₂, he₂, hr₂, htree₂, hf₂⟩ := exec_fillConst baseTree zero (by decide) (by decide) y₁ hb₁
    (by rw [hb₁.hbaseTree]; omega) hfit_a
  have hb₂ : BaseRegs n bC M y₂ := hb₁.of_eq fun i hi => hr₂ i (by omega)
  have hrr₂ : y₂.regs rr = r.val := ((hr₂ rr (by decide)).trans (hr₁ rr (by decide))).trans hr_reg
  have hf_tr : Fits w (bC + n * n + 4 * n + r.val) := hfit.of_le (by have := r.isLt; omega)
  have hstep₃ : ∃ y₃,
      ExecWithin w (ram[ addr ← baseTree + rr; *addr ← one ] : Code .standard 28) y₂ y₃ 2 ∧
      y₃ = (y₂.set addr (bC + n * n + 4 * n + r.val)).write (bC + n * n + 4 * n + r.val) 1 := by
    refine WP.exists_execWithin ?_
    wram_exec [hb₂.hbaseTree, hrr₂, hb₂.hone, hf_tr]
    rfl
  obtain ⟨y₃, he₃, rfl⟩ := hstep₃
  have hb₃ : BaseRegs n bC M
      ((y₂.set addr (bC + n * n + 4 * n + r.val)).write (bC + n * n + 4 * n + r.val) 1) :=
    hb₂.of_eq fun i hi => by wram_simp
  have hrr₃ : ((y₂.set addr (bC + n * n + 4 * n + r.val)).write
      (bC + n * n + 4 * n + r.val) 1).regs rr = r.val := by wram_simp [hrr₂]
  obtain ⟨y₄, he₄, hr₄, hbest₄, hf₄⟩ := exec_fillConst baseBestRow rr (by decide) (by decide) _ hb₃
    (by rw [hb₃.hbaseBestRow]; omega) hfit_a
  have hb₄ : BaseRegs n bC M y₄ := hb₃.of_eq fun i hi => hr₄ i (by omega)
  have hrr₄ : y₄.regs rr = r.val := (hr₄ rr (by decide)).trans hrr₃
  have hout₄ : ∀ a, ¬(bC + n * n + 3 * n ≤ a ∧ a < bC + n * n + 7 * n) → y₄.mem a = x.mem a := by
    intro a ha
    have hne_tr : a ≠ bC + n * n + 4 * n + r.val := by have := r.isLt; omega
    rw [hf₄ a (by rw [hb₃.hbaseBestRow]; omega)]
    change Function.update y₂.mem (bC + n * n + 4 * n + r.val) 1 a = x.mem a
    rw [Function.update_of_ne hne_tr, hf₂ a (by rw [hb₁.hbaseTree]; omega),
      hf₁ a (by rw [hb.hbaseUsed]; omega)]
  have hC₄ : CostMem bC C y₄.mem := hC.of_outside fun a ha => hout₄ a (by omega)
  have hOM₄ : OuterMem bC y₀ z₀ mate₀ y₄.mem :=
    ⟨fun i => (hout₄ _ (by have := i.isLt; omega)).trans (hOM.hy i),
     fun j => (hout₄ _ (by have := j.isLt; omega)).trans (hOM.hnz j),
     fun j => (hout₄ _ (by have := j.isLt; omega)).trans (hOM.hcol j),
     fun j i hm => (hout₄ _ (by have := i.isLt; omega)).trans (hOM.hrow_some j i hm),
     fun i hm => (hout₄ _ (by have := i.isLt; omega)).trans (hOM.hrow_none i hm)⟩
  obtain ⟨y₅, he₅, hr₅, hminv₅, hf₅⟩ := exec_initMinvCode hCW hOB r y₄ hb₄ hC₄ hOM₄ hrr₄ hfit
  have hstep₆ : ∃ y₆,
      ExecWithin w (ram[ augmented ← #0 ] : Code .standard 28) y₅ y₆ 1 ∧
      y₆ = y₅.set augmented 0 := by
    refine WP.exists_execWithin ?_
    wram_exec
    rfl
  obtain ⟨y₆, he₆, rfl⟩ := hstep₆
  have hout₅ : ∀ a, ¬(bC + n * n + 3 * n ≤ a ∧ a < bC + n * n + 7 * n) → y₅.mem a = x.mem a :=
    fun a ha => (hf₅ a (by omega)).trans (hout₄ a ha)
  refine ⟨_, (he₁.seq (he₂.seq (he₃.seq (he₄.seq (he₅.seq he₆))))).mono (by omega),
    fun i hi => ?_, by wram_simp, ?_, hout₅⟩
  · have h5 := hr₅ i (by omega)
    have h4 := hr₄ i (by omega)
    have h2 := hr₂ i (by omega)
    have h1 := hr₁ i (by omega)
    wram_simp [h5, h4, h2, h1]
  · refine ⟨⟨fun i => ?_, fun j => ?_, fun j => ?_, fun j i hm => ?_, fun i hm => ?_⟩,
      fun j => ?_, fun i => ?_, fun j => ?_, fun j => ?_⟩
    · change y₅.mem _ = _
      simpa only [hgInit_y] using (hout₅ _ (by have := i.isLt; omega)).trans (hOM.hy i)
    · change y₅.mem _ = _
      simpa only [hgInit_z] using (hout₅ _ (by have := j.isLt; omega)).trans (hOM.hnz j)
    · change y₅.mem _ = _
      simpa only [hgInit_mate] using (hout₅ _ (by have := j.isLt; omega)).trans (hOM.hcol j)
    · rw [hgInit_mate] at hm
      exact (hout₅ _ (by have := i.isLt; omega)).trans (hOM.hrow_some j i hm)
    · exact (hout₅ _ (by have := i.isLt; omega)).trans (hOM.hrow_none i hm)
    · change y₅.mem (bC + n * n + 3 * n + j.val) = _
      rw [hf₅ _ (by have := j.isLt; omega), hf₄ _ (by rw [hb₃.hbaseBestRow]; have := j.isLt; omega)]
      change Function.update y₂.mem (bC + n * n + 4 * n + r.val) 1 (bC + n * n + 3 * n + j.val) = _
      rw [Function.update_of_ne (by have := j.isLt; have := r.isLt; omega),
        hf₂ _ (by rw [hb₁.hbaseTree]; have := j.isLt; omega)]
      have hu := hused₁ j.val j.isLt
      rw [hb.hbaseUsed, hb.hzero] at hu
      simpa [hgInit_used] using hu
    · change y₅.mem (bC + n * n + 4 * n + i.val) = _
      rw [hf₅ _ (by have := i.isLt; omega), hf₄ _ (by rw [hb₃.hbaseBestRow]; have := i.isLt; omega),
        hgInit_tree]
      change Function.update y₂.mem (bC + n * n + 4 * n + r.val) 1 (bC + n * n + 4 * n + i.val) = _
      by_cases hir : i = r
      · subst hir
        simp
      · have hne : bC + n * n + 4 * n + i.val ≠ bC + n * n + 4 * n + r.val := fun h =>
          hir (Fin.ext (by omega))
        rw [Function.update_of_ne hne]
        have ht := htree₂ i.val i.isLt
        rw [hb₁.hbaseTree, hb₁.hzero] at ht
        simpa [hir] using ht
    · simpa [hgInit_minv] using hminv₅ j
    · change y₅.mem (bC + n * n + 6 * n + j.val) = r.val
      rw [hf₅ _ (by have := j.isLt; omega)]
      have hb_j := hbest₄ j.val j.isLt
      rwa [hb₃.hbaseBestRow, hrr₃] at hb_j

/-! ### Inner round subroutines: argmin, dual update, extend, augment -/

/-- Scan one column `idx` for the minimum-slack unused column. -/
private def argminBody : Code .standard 28 := ram[
  addr ← baseUsed + idx; val ← *addr;
  if val = zero then [
    addr ← baseMinv + idx; val2 ← *addr;
    if rj1 = rn then [ rj1 ← idx; rdelta ← val2 ]
    else [ if val2 < rdelta then [ rj1 ← idx; rdelta ← val2 ] else [ tmp ← zero ] ]
  ] else [ tmp ← zero ];
  idx ← idx + one ]

/-- Compute `hgArgmin s` into `rj1` and its slack into `rdelta`. -/
private def argminCode : Code .standard 28 :=
  .seq (ram[ rj1 ← rn; rdelta ← #0; idx ← #0 ]) (.loop (.lt idx rn) argminBody)

private theorem exec_argminCode {w n bC M W : ℕ} {c : Fin n × Fin n → ℤ} {r : Fin n}
    {s : HgState n} {bestRow : Fin n → Fin n}
    (hSI : HgStepInv c W r s bestRow) (x : Data 28)
    (hb : BaseRegs n bC M x) (hSM : StepMem bC s bestRow x.mem)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y j₁, ExecWithin w argminCode x y (13 * n + 5) ∧
      (∀ i : Fin 28, i.val < 18 → y.regs i = x.regs i) ∧
      y.mem = x.mem ∧
      hgArgmin s = some j₁ ∧
      y.regs rj1 = j₁.val ∧
      y.regs rdelta = (vget s.minv j₁).toNat := by
  let bAt (k : ℕ) : Option (Fin n) := ((List.finRange n).take k).foldl (hgArgminStep s) none
  let P (k : ℕ) (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 18 → y.regs i = x.regs i) ∧
      y.mem = x.mem ∧
      match bAt k with
      | none => y.regs rj1 = n
      | some j₀ => y.regs rj1 = j₀.val ∧ y.regs rdelta = (vget s.minv j₀).toNat
  have hbody (y : Data 28) (hy : P (y.regs idx) y) (hlt : y.regs idx < n) :
      ∃ z, ExecWithin w argminBody y z 11 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hmem, hbAt⟩ := hy
    let j : Fin n := ⟨y.regs idx, hlt⟩
    have hby : BaseRegs n bC M y := hb.of_eq fun i hi => hr i (by omega)
    have hf1 : Fits w (bC + n * n + 3 * n + y.regs idx) := hfit.of_le (by omega)
    have hf2 : Fits w (bC + n * n + 5 * n + y.regs idx) := hfit.of_le (by omega)
    have hf3 : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    have hused_j : y.mem (bC + n * n + 3 * n + y.regs idx) =
        if vget s.used j = true then 1 else 0 := by
      rw [hmem]
      exact hSM.hused j
    have hminv_j : y.mem (bC + n * n + 5 * n + y.regs idx) = (vget s.minv j).toNat := by
      rw [hmem]
      exact hSM.hminv j
    have hb_step : bAt (y.regs idx + 1) = hgArgminStep s (bAt (y.regs idx)) j := by
      simp only [bAt, List.take_succ_finRange hlt, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      rfl
    refine WP.exists_execWithin ?_
    unfold argminBody
    by_cases hu : vget s.used j = true
    · have hu_val : (if vget s.used j = true then 1 else 0) = 1 := ite_eq_left hu
      wram_exec [hby.hbaseUsed, hby.hzero, hby.hone, hused_j, hu_val, hf1, hf3]
      refine ⟨⟨fun i hi => by wram_simp [hr i hi], hmem, ?_⟩, by wram_simp⟩
      rw [hb_step]
      unfold hgArgminStep
      rw [ite_eq_left hu]
      cases hbk : bAt (y.regs idx) with
      | none =>
        rw [hbk] at hbAt
        wram_simp [hbAt]
      | some j₀ =>
        rw [hbk] at hbAt
        exact ⟨by wram_simp [hbAt.1], by wram_simp [hbAt.2]⟩
    · have huf : vget s.used j = false := Bool.eq_false_iff.mpr hu
      have hu_val : (if vget s.used j = true then 1 else 0) = 0 := ite_eq_right hu
      cases hbk : bAt (y.regs idx) with
      | none =>
        rw [hbk] at hbAt
        wram_exec [hby.hbaseUsed, hby.hbaseMinv, hby.hzero, hby.hone, hby.hrn,
          hused_j, hu_val, hminv_j, hbAt, hf1, hf2, hf3]
        refine ⟨⟨fun i hi => by wram_simp [hr i hi], hmem, ?_⟩, by wram_simp⟩
        rw [hb_step]
        unfold hgArgminStep
        rw [ite_eq_right hu, hbk]
        exact ⟨by wram_simp; rfl, by wram_simp⟩
      | some j₀ =>
        rw [hbk] at hbAt
        obtain ⟨hrj1, hrdelta⟩ := hbAt
        have hj₀_ne : j₀.val ≠ n := ne_of_lt j₀.isLt
        have hm_j := (hSI.minv_bounds j).1
        have hm_j₀ := (hSI.minv_bounds j₀).1
        by_cases hlt_m : (vget s.minv j).toNat < (vget s.minv j₀).toNat
        · have hlt_z : vget s.minv j < vget s.minv j₀ := by omega
          wram_exec [hby.hbaseUsed, hby.hbaseMinv, hby.hzero, hby.hone, hby.hrn,
            hused_j, hu_val, hminv_j, hrj1, hrdelta, hj₀_ne, hlt_m, hf1, hf2, hf3]
          refine ⟨⟨fun i hi => by wram_simp [hr i hi], hmem, ?_⟩, by wram_simp⟩
          rw [hb_step]
          unfold hgArgminStep
          rw [ite_eq_right hu, hbk]
          dsimp only
          rw [ite_eq_left hlt_z]
          exact ⟨by wram_simp; rfl, by wram_simp⟩
        · have hlt_z : ¬vget s.minv j < vget s.minv j₀ := by omega
          wram_exec [hby.hbaseUsed, hby.hbaseMinv, hby.hzero, hby.hone, hby.hrn,
            hused_j, hu_val, hminv_j, hrj1, hrdelta, hj₀_ne, hlt_m, hf1, hf2, hf3]
          refine ⟨⟨fun i hi => by wram_simp [hr i hi], hmem, ?_⟩, by wram_simp⟩
          rw [hb_step]
          unfold hgArgminStep
          rw [ite_eq_right hu, hbk]
          dsimp only
          rw [ite_eq_right hlt_z]
          exact ⟨by wram_simp [hrj1], by wram_simp [hrdelta]⟩
  have hsetup : ∃ y₀,
      ExecWithin w (ram[ rj1 ← rn; rdelta ← #0; idx ← #0 ] : Code .standard 28) x y₀ 3 ∧
      P 0 y₀ ∧ y₀.regs idx = 0 := by
    refine WP.exists_execWithin ?_
    wram_exec [hb.hrn]
    exact ⟨⟨fun i hi => by wram_simp, rfl, by
      dsimp only [bAt, List.take, List.foldl]
      wram_simp [hb.hrn]⟩, by wram_simp⟩
  obtain ⟨y₀, hs₀, hP₀, hidx₀⟩ := hsetup
  obtain ⟨y, hl, hPn, _⟩ := ExecWithin.loop_count P
    (fun y hy => (hy.1 rn (by decide)).trans hb.hrn) hbody (by omega) (hidx₀ ▸ hP₀)
  obtain ⟨hr, hmem, hb_n⟩ := hPn
  have hbn_eq : bAt n = hgArgmin s := by
    simp [bAt, hgArgmin, List.take_of_length_le (show (List.finRange n).length ≤ n by simp)]
  rw [hbn_eq] at hb_n
  cases ha : hgArgmin s with
  | none =>
    have h1 := usedCount_all (hgArgmin_none ha)
    have h2 := usedCount_le hSI.matching hSI.used_mate
    have h3 := card_lt_of_root_free hSI.matching hSI.root_free
    omega
  | some j₁ =>
    rw [ha] at hb_n
    exact ⟨y, j₁, (hs₀.seq hl).mono (by rw [hidx₀]; omega), hr, hmem, rfl, hb_n.1, hb_n.2⟩

/-- Conditional vector addition body: if `flag[idx] = 1` then `target[idx] += rdelta`. -/
private def condAddBody (flagBase targetBase : Fin 28) : Code .standard 28 := ram[
  addr ← flagBase + idx; val ← *addr;
  addr ← targetBase + idx; val2 ← *addr;
  if val = one then [ val2 ← val2 + rdelta ] else [ tmp ← zero ];
  *addr ← val2; idx ← idx + one ]

/-- Conditional vector addition loop over `0 .. n - 1`. -/
private def condAddCode (flagBase targetBase : Fin 28) : Code .standard 28 :=
  .seq (ram[ idx ← #0 ]) (.loop (.lt idx rn) (condAddBody flagBase targetBase))

/-- Dual slack update body (`minv[j] -= rdelta` on unused columns). -/
private def dualMinvBody : Code .standard 28 := ram[
  addr ← baseUsed + idx; val ← *addr;
  addr ← baseMinv + idx; val2 ← *addr;
  if val = zero then [ val2 ← val2 - rdelta ] else [ tmp ← zero ];
  *addr ← val2; idx ← idx + one ]

/-- Dual slack update loop. -/
private def dualMinvCode : Code .standard 28 :=
  .seq (ram[ idx ← #0 ]) (.loop (.lt idx rn) dualMinvBody)

/-- Complete `O(n)` dual update `hgDual s (vget s.minv j₁)`. -/
private def dualCode : Code .standard 28 :=
  .seq (condAddCode baseTree baseY) (.seq (condAddCode baseUsed baseNZ) dualMinvCode)

private theorem exec_condAddCode {w n bC M : ℕ}
    (flagBase targetBase : Fin 28) (hf_lt : flagBase.val < 21) (ht_lt : targetBase.val < 21)
    {bF bT delta : ℕ} {flag : Fin n → Bool} {cur : Fin n → ℕ}
    (x : Data 28) (hb : BaseRegs n bC M x)
    (hbF : x.regs flagBase = bF) (hbT : x.regs targetBase = bT)
    (hdisj : bT + n ≤ bF ∨ bF + n ≤ bT)
    (hdelta : x.regs rdelta = delta)
    (hflag : ∀ k : Fin n, x.mem (bF + k.val) = if flag k = true then 1 else 0)
    (hcur : ∀ k : Fin n, x.mem (bT + k.val) = cur k)
    (hfitF : Fits w (bF + n)) (hfitT : Fits w (bT + n)) (hfitN : Fits w (n + 1))
    (hfitAdd : ∀ k : Fin n, flag k = true → Fits w (cur k + delta)) :
    ∃ y, ExecWithin w (condAddCode flagBase targetBase) x y (11 * n + 3) ∧
      (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ k : Fin n, y.mem (bT + k.val) = if flag k = true then cur k + delta else cur k) ∧
      (∀ a, ¬(bT ≤ a ∧ a < bT + n) → y.mem a = x.mem a) := by
  let e : ℕ → ℕ := fun k =>
    if hk : k < n then if flag ⟨k, hk⟩ = true then cur ⟨k, hk⟩ + delta else cur ⟨k, hk⟩ else 0
  let P (k : ℕ) (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ j < k, y.mem (bT + j) = e j) ∧
      (∀ a, ¬(bT ≤ a ∧ a < bT + k) → y.mem a = x.mem a)
  have hbody (y : Data 28) (hy : P (y.regs idx) y) (hlt : y.regs idx < n) :
      ∃ z, ExecWithin w (condAddBody flagBase targetBase) y z 9 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hm, hf⟩ := hy
    let k₀ : Fin n := ⟨y.regs idx, hlt⟩
    have hby : BaseRegs n bC M y := hb.of_eq fun i hi => hr i (by omega)
    have hbF_y : y.regs flagBase = bF := (hr flagBase hf_lt).trans hbF
    have hbT_y : y.regs targetBase = bT := (hr targetBase ht_lt).trans hbT
    have hdel_y : y.regs rdelta = delta := (hr rdelta (by decide)).trans hdelta
    have hfk : y.mem (bF + y.regs idx) = if flag k₀ = true then 1 else 0 := by
      rw [hf _ (by omega)]
      exact hflag k₀
    have hck : y.mem (bT + y.regs idx) = cur k₀ := by
      rw [hf _ (by omega)]
      exact hcur k₀
    have hf1 : Fits w (bF + y.regs idx) := hfitF.of_le (by omega)
    have hf2 : Fits w (bT + y.regs idx) := hfitT.of_le (by omega)
    have hf3 : Fits w (y.regs idx + 1) := hfitN.of_le (by omega)
    have hta : targetBase ≠ addr := fun h => by subst h; simp at ht_lt
    have htv : targetBase ≠ val := fun h => by subst h; simp at ht_lt
    have hstep : ∃ z, ExecWithin w (condAddBody flagBase targetBase) y z 9 ∧
        z.mem = Function.update y.mem (bT + y.regs idx) (e (y.regs idx)) ∧
        (∀ i : Fin 28, i.val < 21 → z.regs i = x.regs i) ∧
        z.regs idx = y.regs idx + 1 := by
      refine WP.exists_execWithin ?_
      unfold condAddBody
      by_cases ht : flag k₀ = true
      · have ht_val : (if flag k₀ = true then 1 else 0) = 1 := ite_eq_left ht
        have heq_e : cur k₀ + delta = e (y.regs idx) := by
          simp only [e, hlt, dite_true]
          exact (ite_eq_left ht).symm
        have hf4 : Fits w (cur k₀ + delta) := hfitAdd k₀ ht
        wram_exec [hbF_y, hbT_y, hta, htv, hby.hone, hby.hzero, hdel_y,
          hfk, ht_val, hck, hf1, hf2, hf3, hf4]
        exact ⟨by wram_simp [hta, htv, hbT_y, heq_e], fun i hi => by wram_simp [hr i hi],
          by wram_simp⟩
      · have ht_val : (if flag k₀ = true then 1 else 0) = 0 := ite_eq_right ht
        have heq_e : cur k₀ = e (y.regs idx) := by
          simp only [e, hlt, dite_true]
          exact (ite_eq_right ht).symm
        wram_exec [hbF_y, hbT_y, hta, htv, hby.hone, hby.hzero, hdel_y,
          hfk, ht_val, hck, hf1, hf2, hf3]
        exact ⟨by wram_simp [hta, htv, hbT_y, hck, heq_e], fun i hi => by wram_simp [hr i hi],
          by wram_simp⟩
    obtain ⟨z, he, hmz, hrz, hiz⟩ := hstep
    obtain ⟨hm', hf'⟩ := prefix_write_step hm hf hmz
    exact ⟨z, he, ⟨hrz, hm', hf'⟩, hiz⟩
  obtain ⟨y, he, hr, hm, hf⟩ := exec_forLoop P
    (fun y hy => (hy.1 rn (by decide)).trans hb.hrn) hbody (x := x)
    ⟨fun i hi => by wram_simp, fun _ hj => by omega, fun _ _ => rfl⟩
  refine ⟨y, he.mono (by omega), hr, fun k => ?_, hf⟩
  simpa [e, k.isLt] using hm k.val k.isLt

private theorem exec_dualYCode {w n bC M W : ℕ} {C : Fin n × Fin n → ℕ} {r j₁ : Fin n}
    {s : HgState n} {bestRow : Fin n → Fin n}
    (hCW : ∀ u v, C (u, v) ≤ W)
    (hSI : HgStepInv (fun p => (C p : ℤ)) W r s bestRow)
    (hj₁ : vget s.used j₁ = false)
    (hmin : ∀ j, vget s.used j = false → vget s.minv j₁ ≤ vget s.minv j)
    (x : Data 28) (hb : BaseRegs n bC M x) (hSM : StepMem bC s bestRow x.mem)
    (hdelta : x.regs rdelta = (vget s.minv j₁).toNat)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y, ExecWithin w (condAddCode baseTree baseY) x y (11 * n + 3) ∧
      (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ i : Fin n, y.mem (bC + n * n + i.val) = (vget (hgDual s (vget s.minv j₁)).y i).toNat) ∧
      (∀ a, ¬(bC + n * n ≤ a ∧ a < bC + n * n + n) → y.mem a = x.mem a) := by
  have hSD := hgStepInv_dual (c := fun p => (C p : ℤ))
    (fun u v => ⟨Nat.cast_nonneg _, Nat.cast_le.mpr (hCW u v)⟩) hSI hj₁ hmin
  obtain ⟨y, he, hr, hm, hf⟩ := exec_condAddCode baseTree baseY (by decide) (by decide)
    x hb hb.hbaseTree hb.hbaseY (.inl (by omega)) hdelta hSM.htree hSM.hy
    (hfit.of_le (by omega)) (hfit.of_le (by omega)) (hfit.of_le (by omega)) fun i₀ ht => by
      have hyb := hSI.y_bounds i₀
      have hdb := hSI.minv_bounds j₁
      have hyDb := hSD.y_bounds i₀
      rw [hgDual_y, ite_eq_left ht] at hyDb
      exact hfit.of_le (by omega)
  refine ⟨y, he, hr, fun i₀ => ?_, hf⟩
  rw [hm i₀, hgDual_y]
  have hyb := hSI.y_bounds i₀
  have hdb := hSI.minv_bounds j₁
  by_cases ht : vget s.tree i₀ = true
  · rw [ite_eq_left ht, ite_eq_left ht]; omega
  · rw [ite_eq_right ht, ite_eq_right ht]

private theorem exec_dualNZCode {w n bC M W : ℕ} {C : Fin n × Fin n → ℕ} {r j₁ : Fin n}
    {s : HgState n} {bestRow : Fin n → Fin n}
    (hCW : ∀ u v, C (u, v) ≤ W)
    (hSI : HgStepInv (fun p => (C p : ℤ)) W r s bestRow)
    (hj₁ : vget s.used j₁ = false)
    (hmin : ∀ j, vget s.used j = false → vget s.minv j₁ ≤ vget s.minv j)
    (x : Data 28) (hb : BaseRegs n bC M x)
    (hused_x : ∀ j : Fin n, x.mem (bC + n * n + 3 * n + j.val) =
      if vget s.used j = true then 1 else 0)
    (hnz_x : ∀ j : Fin n, x.mem (bC + n * n + n + j.val) = (-vget s.z j).toNat)
    (hdelta : x.regs rdelta = (vget s.minv j₁).toNat)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y, ExecWithin w (condAddCode baseUsed baseNZ) x y (11 * n + 3) ∧
      (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ j : Fin n,
        y.mem (bC + n * n + n + j.val) = (-vget (hgDual s (vget s.minv j₁)).z j).toNat) ∧
      (∀ a, ¬(bC + n * n + n ≤ a ∧ a < bC + n * n + 2 * n) → y.mem a = x.mem a) := by
  have hSD := hgStepInv_dual (c := fun p => (C p : ℤ))
    (fun u v => ⟨Nat.cast_nonneg _, Nat.cast_le.mpr (hCW u v)⟩) hSI hj₁ hmin
  obtain ⟨y, he, hr, hm, hf⟩ := exec_condAddCode baseUsed baseNZ (by decide) (by decide)
    x hb hb.hbaseUsed hb.hbaseNZ (.inl (by omega)) hdelta hused_x hnz_x
    (hfit.of_le (by omega)) (hfit.of_le (by omega)) (hfit.of_le (by omega)) fun j hu => by
      have hzb := hSI.z_bounds j
      have hdb := hSI.minv_bounds j₁
      have hzDb := hSD.z_bounds j
      rw [hgDual_z, ite_eq_left hu] at hzDb
      exact hfit.of_le (by omega)
  refine ⟨y, he, hr, fun j => ?_, fun a ha => hf a (by omega)⟩
  rw [hm j, hgDual_z]
  have hzb := hSI.z_bounds j
  have hdb := hSI.minv_bounds j₁
  by_cases hu : vget s.used j = true
  · rw [ite_eq_left hu, ite_eq_left hu]; omega
  · rw [ite_eq_right hu, ite_eq_right hu]

private theorem exec_dualMinvCode {w n bC M W : ℕ} {c : Fin n × Fin n → ℤ} {r j₁ : Fin n}
    {s : HgState n} {bestRow : Fin n → Fin n}
    (hSI : HgStepInv c W r s bestRow)
    (hmin : ∀ j, vget s.used j = false → vget s.minv j₁ ≤ vget s.minv j)
    (x : Data 28) (hb : BaseRegs n bC M x)
    (hused_x : ∀ j : Fin n, x.mem (bC + n * n + 3 * n + j.val) =
      if vget s.used j = true then 1 else 0)
    (hminv_x : ∀ j : Fin n, x.mem (bC + n * n + 5 * n + j.val) = (vget s.minv j).toNat)
    (hdelta : x.regs rdelta = (vget s.minv j₁).toNat)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y, ExecWithin w dualMinvCode x y (11 * n + 3) ∧
      (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ j : Fin n, y.mem (bC + n * n + 5 * n + j.val) =
        (vget (hgDual s (vget s.minv j₁)).minv j).toNat) ∧
      (∀ a, ¬(bC + n * n + 5 * n ≤ a ∧ a < bC + n * n + 6 * n) → y.mem a = x.mem a) := by
  let d := bC + n * n + 5 * n
  let e : ℕ → ℕ := fun k =>
    if hk : k < n then (vget (hgDual s (vget s.minv j₁)).minv ⟨k, hk⟩).toNat else 0
  let P (k : ℕ) (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ j < k, y.mem (d + j) = e j) ∧
      (∀ a, ¬(d ≤ a ∧ a < d + k) → y.mem a = x.mem a)
  have hbody (y : Data 28) (hy : P (y.regs idx) y) (hlt : y.regs idx < n) :
      ∃ z, ExecWithin w dualMinvBody y z 9 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hm, hf⟩ := hy
    let j : Fin n := ⟨y.regs idx, hlt⟩
    have hby : BaseRegs n bC M y := hb.of_eq fun i hi => hr i (by omega)
    have hdel_y : y.regs rdelta = (vget s.minv j₁).toNat := (hr rdelta (by decide)).trans hdelta
    have hu_j : y.mem (bC + n * n + 3 * n + y.regs idx) =
        if vget s.used j = true then 1 else 0 := by
      rw [hf _ (by omega)]
      exact hused_x j
    have hm_j : y.mem (bC + n * n + 5 * n + y.regs idx) = (vget s.minv j).toNat := by
      rw [hf _ (by simp only [d]; omega)]
      exact hminv_x j
    have hmb := hSI.minv_bounds j
    have hdb := hSI.minv_bounds j₁
    have hf1 : Fits w (bC + n * n + 3 * n + y.regs idx) := hfit.of_le (by omega)
    have hf2 : Fits w (d + y.regs idx) := hfit.of_le (by omega)
    have hf3 : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    have hstep : ∃ z, ExecWithin w dualMinvBody y z 9 ∧
        z.mem = Function.update y.mem (d + y.regs idx) (e (y.regs idx)) ∧
        (∀ i : Fin 28, i.val < 21 → z.regs i = x.regs i) ∧
        z.regs idx = y.regs idx + 1 := by
      refine WP.exists_execWithin ?_
      unfold dualMinvBody
      by_cases hu : vget s.used j = true
      · have hu_val : (if vget s.used j = true then 1 else 0) = 1 := ite_eq_left hu
        have heq_e : (vget s.minv j).toNat = e (y.regs idx) := by
          simp only [e, hlt, dite_true]
          change _ = (vget (hgDual s (vget s.minv j₁)).minv j).toNat
          rw [hgDual_minv, ite_eq_left hu]
        wram_exec [hby.hbaseUsed, hby.hbaseMinv, hby.hone, hby.hzero, hdel_y,
          hu_j, hu_val, hm_j, hf1, hf2, hf3]
        exact ⟨by wram_simp [d, heq_e], fun i hi => by wram_simp [hr i hi], by wram_simp⟩
      · have huf : vget s.used j = false := Bool.eq_false_iff.mpr hu
        have hu_val : (if vget s.used j = true then 1 else 0) = 0 := ite_eq_right hu
        have hle_m : (vget s.minv j₁).toNat ≤ (vget s.minv j).toNat := by
          have := hmin j huf
          omega
        have heq_e : (vget s.minv j).toNat - (vget s.minv j₁).toNat = e (y.regs idx) := by
          simp only [e, hlt, dite_true]
          change _ = (vget (hgDual s (vget s.minv j₁)).minv j).toNat
          rw [hgDual_minv, ite_eq_right hu]
          have := hmin j huf
          omega
        have hf4 : Fits w ((vget s.minv j).toNat - (vget s.minv j₁).toNat) := hfit.of_le (by omega)
        wram_exec [hby.hbaseUsed, hby.hbaseMinv, hby.hone, hby.hzero, hdel_y,
          hu_j, hu_val, hm_j, hle_m, hf1, hf2, hf3, hf4]
        exact ⟨by wram_simp [d, heq_e], fun i hi => by wram_simp [hr i hi], by wram_simp⟩
    obtain ⟨z, he, hmz, hrz, hiz⟩ := hstep
    obtain ⟨hm', hf'⟩ := prefix_write_step hm hf hmz
    exact ⟨z, he, ⟨hrz, hm', hf'⟩, hiz⟩
  obtain ⟨y, he, hr, hm, hf⟩ := exec_forLoop P
    (fun y hy => (hy.1 rn (by decide)).trans hb.hrn) hbody (x := x)
    ⟨fun i hi => by wram_simp, fun _ hj => by omega, fun _ _ => rfl⟩
  refine ⟨y, he.mono (by omega), hr, fun j => ?_, fun a ha => hf a (by simp only [d]; omega)⟩
  simpa [d, e, j.isLt] using hm j.val j.isLt

private theorem exec_dualCode {w n bC M W : ℕ} {C : Fin n × Fin n → ℕ} {r j₁ : Fin n}
    {s : HgState n} {bestRow : Fin n → Fin n}
    (hCW : ∀ u v, C (u, v) ≤ W)
    (hSI : HgStepInv (fun p => (C p : ℤ)) W r s bestRow)
    (hj₁ : vget s.used j₁ = false)
    (hmin : ∀ j, vget s.used j = false → vget s.minv j₁ ≤ vget s.minv j)
    (x : Data 28) (hb : BaseRegs n bC M x) (hSM : StepMem bC s bestRow x.mem)
    (hdelta : x.regs rdelta = (vget s.minv j₁).toNat)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y, ExecWithin w dualCode x y (33 * n + 9) ∧
      (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      StepMem bC (hgDual s (vget s.minv j₁)) bestRow y.mem ∧
      (∀ a, a < bC + n * n ∨ bC + n * n + 6 * n ≤ a → y.mem a = x.mem a) := by
  obtain ⟨y₁, he₁, hr₁, hy₁, hf₁⟩ := exec_dualYCode hCW hSI hj₁ hmin x hb hSM hdelta hfit
  have hb₁ : BaseRegs n bC M y₁ := hb.of_eq fun i hi => hr₁ i (by omega)
  have hdel₁ : y₁.regs rdelta = (vget s.minv j₁).toNat := (hr₁ rdelta (by decide)).trans hdelta
  have hused₁ : ∀ j : Fin n, y₁.mem (bC + n * n + 3 * n + j.val) =
      if vget s.used j = true then 1 else 0 :=
    fun j => (hf₁ _ (by have := j.isLt; omega)).trans (hSM.hused j)
  have hnz₁ : ∀ j : Fin n, y₁.mem (bC + n * n + n + j.val) = (-vget s.z j).toNat :=
    fun j => (hf₁ _ (by have := j.isLt; omega)).trans (hSM.hnz j)
  obtain ⟨y₂, he₂, hr₂, hnz₂, hf₂⟩ :=
    exec_dualNZCode hCW hSI hj₁ hmin y₁ hb₁ hused₁ hnz₁ hdel₁ hfit
  have hb₂ : BaseRegs n bC M y₂ := hb₁.of_eq fun i hi => hr₂ i (by omega)
  have hdel₂ : y₂.regs rdelta = (vget s.minv j₁).toNat := (hr₂ rdelta (by decide)).trans hdel₁
  have hused₂ : ∀ j : Fin n, y₂.mem (bC + n * n + 3 * n + j.val) =
      if vget s.used j = true then 1 else 0 :=
    fun j => (hf₂ _ (by have := j.isLt; omega)).trans (hused₁ j)
  have hminv₂ : ∀ j : Fin n, y₂.mem (bC + n * n + 5 * n + j.val) = (vget s.minv j).toNat :=
    fun j => (hf₂ _ (by have := j.isLt; omega)).trans
      ((hf₁ _ (by have := j.isLt; omega)).trans (hSM.hminv j))
  obtain ⟨y₃, he₃, hr₃, hminv₃, hf₃⟩ :=
    exec_dualMinvCode hSI hmin y₂ hb₂ hused₂ hminv₂ hdel₂ hfit
  have hout : ∀ a, ¬(bC + n * n ≤ a ∧ a < bC + n * n + 2 * n) ∧
      ¬(bC + n * n + 5 * n ≤ a ∧ a < bC + n * n + 6 * n) → y₃.mem a = x.mem a :=
    fun a ⟨ha1, ha2⟩ => (hf₃ a ha2).trans ((hf₂ a (by omega)).trans (hf₁ a (by omega)))
  refine ⟨y₃, (he₁.seq (he₂.seq he₃)).mono (by omega),
    fun i hi => ((hr₃ i hi).trans (hr₂ i hi)).trans (hr₁ i hi),
    ⟨⟨fun i => ?_, fun j => ?_, fun j => ?_, fun j i hm => ?_, fun i hm => ?_⟩,
      fun j => ?_, fun i => ?_, hminv₃, fun j => ?_⟩,
    fun a ha => hout a (by omega)⟩
  · rw [hf₃ _ (by have := i.isLt; omega), hf₂ _ (by have := i.isLt; omega)]
    exact hy₁ i
  · rw [hf₃ _ (by have := j.isLt; omega)]
    exact hnz₂ j
  · exact (hout _ (by have := j.isLt; omega)).trans (hSM.hcol j)
  · exact (hout _ (by have := i.isLt; omega)).trans (hSM.hrow_some j i hm)
  · exact (hout _ (by have := i.isLt; omega)).trans (hSM.hrow_none i hm)
  · exact (hout _ (by have := j.isLt; omega)).trans (hSM.hused j)
  · exact (hout _ (by have := i.isLt; omega)).trans (hSM.htree i)
  · exact (hout _ (by have := j.isLt; omega)).trans (hSM.hbest j)

/-- Update `bestRow[idx]` if `idx` is unused and relaxing via `ri0` strictly lowers slack. -/
private def relaxBestRowBody : Code .standard 28 := ram[
  addr ← baseBestRow + idx; val2 ← *addr;
  addr ← baseUsed + idx; val ← *addr;
  if val = zero then [
    addr ← ri0 * rn; addr ← addr + idx; addr ← baseC + addr; val ← *addr;
    addr ← baseNZ + idx; tmp ← *addr; val ← val + tmp;
    addr ← baseY + ri0; tmp ← *addr; val ← val - tmp;
    addr ← baseMinv + idx; tmp ← *addr;
    if val < tmp then [ val2 ← ri0 ] else [ tmp ← zero ]
  ] else [ tmp ← zero ];
  addr ← baseBestRow + idx; *addr ← val2; idx ← idx + one ]

/-- Update `bestRow` across all columns. -/
private def relaxBestRowCode : Code .standard 28 :=
  .seq (ram[ idx ← #0 ]) (.loop (.lt idx rn) relaxBestRowBody)

/-- Update `minv[idx]` if `idx` is unused and relaxing via `ri0` lowers slack. -/
private def relaxMinvBody : Code .standard 28 := ram[
  addr ← baseMinv + idx; val2 ← *addr;
  addr ← baseUsed + idx; val ← *addr;
  if val = zero then [
    addr ← ri0 * rn; addr ← addr + idx; addr ← baseC + addr; val ← *addr;
    addr ← baseNZ + idx; tmp ← *addr; val ← val + tmp;
    addr ← baseY + ri0; tmp ← *addr; val ← val - tmp;
    if val < val2 then [ val2 ← val ] else [ tmp ← zero ]
  ] else [ tmp ← zero ];
  addr ← baseMinv + idx; *addr ← val2; idx ← idx + one ]

/-- Update `minv` across all columns. -/
private def relaxMinvCode : Code .standard 28 :=
  .seq (ram[ idx ← #0 ]) (.loop (.lt idx rn) relaxMinvBody)

/-- Extend the tree by `rj1` and its mate `ri0`, then relax `bestRow` and `minv`. -/
private def extendCode : Code .standard 28 :=
  .seq (ram[ addr ← baseUsed + rj1; *addr ← one; addr ← baseTree + ri0; *addr ← one ])
    (.seq relaxBestRowCode relaxMinvCode)

private theorem exec_extendCode {w n bC M W : ℕ} {C : Fin n × Fin n → ℕ} {r j₁ i₀ : Fin n}
    {s : HgState n} {bestRow : Fin n → Fin n}
    (hCW : ∀ u v, C (u, v) ≤ W)
    (hSI : HgStepInv (fun p => (C p : ℤ)) W r s bestRow)
    (x : Data 28) (hb : BaseRegs n bC M x)
    (hC : CostMem bC C x.mem) (hSM : StepMem bC s bestRow x.mem)
    (hrj1 : x.regs rj1 = j₁.val) (hri0 : x.regs ri0 = i₀.val)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y, ExecWithin w extendCode x y (48 * n + 10) ∧
      (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      StepMem bC (hgExtend (fun p => (C p : ℤ)) s j₁ i₀)
        (fun j => if vget (vset s.used j₁ true) j = false ∧
          hgRed (fun p => (C p : ℤ)) s.y s.z i₀ j < vget s.minv j then i₀ else bestRow j) y.mem ∧
      (∀ a, a < bC + n * n ∨ bC + n * n + 7 * n ≤ a → y.mem a = x.mem a) := by
  let c : Fin n × Fin n → ℤ := fun p => (C p : ℤ)
  let used' := vset s.used j₁ true
  let tree' := vset s.tree i₀ true
  let bestRow' : Fin n → Fin n := fun j =>
    if vget used' j = false ∧ hgRed c s.y s.z i₀ j < vget s.minv j then i₀ else bestRow j
  have hf_u1 : Fits w (bC + n * n + 3 * n + j₁.val) := hfit.of_le (by have := j₁.isLt; omega)
  have hf_t0 : Fits w (bC + n * n + 4 * n + i₀.val) := hfit.of_le (by have := i₀.isLt; omega)
  have hstep₀ : ∃ y₀,
      ExecWithin w (ram[ addr ← baseUsed + rj1; *addr ← one; addr ← baseTree + ri0; *addr ← one ])
        x y₀ 4 ∧
      (∀ i : Fin 28, i.val < 21 → y₀.regs i = x.regs i) ∧
      y₀.mem = Function.update (Function.update x.mem (bC + n * n + 3 * n + j₁.val) 1)
        (bC + n * n + 4 * n + i₀.val) 1 := by
    refine WP.exists_execWithin ?_
    wram_exec [hb.hbaseUsed, hb.hbaseTree, hb.hone, hrj1, hri0, hf_u1, hf_t0]
    exact ⟨fun i hi => by wram_simp, rfl⟩
  obtain ⟨y₀, he₀, hr₀, hm₀⟩ := hstep₀
  have hused₀ : ∀ j : Fin n, y₀.mem (bC + n * n + 3 * n + j.val) =
      if vget used' j = true then 1 else 0 := by
    intro j
    rw [hm₀, Function.update_of_ne (by have := j.isLt; have := i₀.isLt; omega)]
    by_cases hjj : j = j₁
    · subst hjj
      simp [used']
    · have hne : bC + n * n + 3 * n + j.val ≠ bC + n * n + 3 * n + j₁.val := fun h =>
        hjj (Fin.ext (by omega))
      rw [Function.update_of_ne hne, hSM.hused j]
      simp [used', vget_vset_ne _ _ (Ne.symm hjj)]
  have htree₀ : ∀ i : Fin n, y₀.mem (bC + n * n + 4 * n + i.val) =
      if vget tree' i = true then 1 else 0 := by
    intro i
    rw [hm₀]
    by_cases hii : i = i₀
    · subst hii
      simp [tree']
    · have hne : bC + n * n + 4 * n + i.val ≠ bC + n * n + 4 * n + i₀.val := fun h =>
        hii (Fin.ext (by omega))
      rw [Function.update_of_ne hne,
        Function.update_of_ne (by have := i.isLt; have := j₁.isLt; omega), hSM.htree i]
      simp [tree', vget_vset_ne _ _ (Ne.symm hii)]
  have hout₀ : ∀ a, ¬(bC + n * n + 3 * n ≤ a ∧ a < bC + n * n + 5 * n) → y₀.mem a = x.mem a := by
    intro a ha
    rw [hm₀, Function.update_of_ne (by have := i₀.isLt; omega),
      Function.update_of_ne (by have := j₁.isLt; omega)]
  -- Loop 1: relaxBestRowCode
  let dB := bC + n * n + 6 * n
  let eB : ℕ → ℕ := fun k => if hk : k < n then (bestRow' ⟨k, hk⟩).val else 0
  let PB (k : ℕ) (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ j < k, y.mem (dB + j) = eB j) ∧
      (∀ a, ¬(dB ≤ a ∧ a < dB + k) → y.mem a = y₀.mem a)
  have hbodyB (y : Data 28) (hy : PB (y.regs idx) y) (hlt : y.regs idx < n) :
      ∃ z, ExecWithin w relaxBestRowBody y z 23 ∧ PB (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hm, hf⟩ := hy
    let j : Fin n := ⟨y.regs idx, hlt⟩
    have hby : BaseRegs n bC M y := hb.of_eq fun i hi => hr i (by omega)
    have hri0_y : y.regs ri0 = i₀.val := (hr ri0 (by decide)).trans hri0
    have hbest_j : y.mem (bC + n * n + 6 * n + y.regs idx) = (bestRow j).val := by
      rw [hf _ (by simp only [dB]; omega), hout₀ _ (by have := j.isLt; omega)]
      exact hSM.hbest j
    have hu_j : y.mem (bC + n * n + 3 * n + y.regs idx) =
        if vget used' j = true then 1 else 0 := by
      rw [hf _ (by simp only [dB]; omega)]
      exact hused₀ j
    have hmul : i₀.val * n + y.regs idx < n * n := Cslib.Matrix.pairIndex_lt (i₀, j)
    obtain ⟨hle_sub, hsum_le, hred_eq⟩ := hgRed_nat_eq (hCW i₀ j) (hSI.y_bounds i₀)
      (hSI.z_bounds j) (hSI.feas i₀ j)
    have hC_ij : y.mem (bC + (i₀.val * n + y.regs idx)) = C (i₀, j) := by
      rw [hf _ (by simp only [dB]; omega), hout₀ _ (by omega)]
      exact hC i₀ j
    have hnz_j : y.mem (bC + n * n + n + y.regs idx) = (-vget s.z j).toNat := by
      rw [hf _ (by simp only [dB]; omega), hout₀ _ (by omega)]
      exact hSM.hnz j
    have hy_i : y.mem (bC + n * n + i₀.val) = (vget s.y i₀).toNat := by
      rw [hf _ (by simp only [dB]; omega), hout₀ _ (by have := i₀.isLt; omega)]
      exact hSM.hy i₀
    have hm_j : y.mem (bC + n * n + 5 * n + y.regs idx) = (vget s.minv j).toNat := by
      rw [hf _ (by simp only [dB]; omega), hout₀ _ (by omega)]
      exact hSM.hminv j
    have hm_nonneg := (hSI.minv_bounds j).1
    have hred_nonneg : 0 ≤ hgRed c s.y s.z i₀ j := hSI.feas i₀ j
    have hred_eq' : C (i₀, j) + (-vget s.z j).toNat - (vget s.y i₀).toNat =
        (hgRed c s.y s.z i₀ j).toNat := hred_eq
    have hf1 : Fits w (dB + y.regs idx) := hfit.of_le (by simp only [dB]; omega)
    have hf2 : Fits w (bC + n * n + 3 * n + y.regs idx) := hfit.of_le (by omega)
    have hf3 : Fits w (i₀.val * n) := hfit.of_le (by omega)
    have hf4 : Fits w (i₀.val * n + y.regs idx) := hfit.of_le (by omega)
    have hf5 : Fits w (bC + (i₀.val * n + y.regs idx)) := hfit.of_le (by omega)
    have hf6 : Fits w (bC + n * n + n + y.regs idx) := hfit.of_le (by omega)
    have hf7 : Fits w (C (i₀, j) + (-vget s.z j).toNat) := hfit.of_le (by omega)
    have hf8 : Fits w (bC + n * n + i₀.val) := hfit.of_le (by have := i₀.isLt; omega)
    have hf9 : Fits w (C (i₀, j) + (-vget s.z j).toNat - (vget s.y i₀).toNat) :=
      hfit.of_le (by omega)
    have hf10 : Fits w (bC + n * n + 5 * n + y.regs idx) := hfit.of_le (by omega)
    have hf11 : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    have hstep : ∃ z, ExecWithin w relaxBestRowBody y z 23 ∧
        z.mem = Function.update y.mem (dB + y.regs idx) (eB (y.regs idx)) ∧
        (∀ i : Fin 28, i.val < 21 → z.regs i = x.regs i) ∧
        z.regs idx = y.regs idx + 1 := by
      refine WP.exists_execWithin ?_
      unfold relaxBestRowBody
      by_cases hu : vget used' j = true
      · have hu_val : (if vget used' j = true then 1 else 0) = 1 := ite_eq_left hu
        have heq_e : (bestRow j).val = eB (y.regs idx) := by
          simp only [eB, hlt, dite_true]
          change _ = (bestRow' j).val
          simp [bestRow', hu]
        wram_exec [hby.hbaseBestRow, hby.hbaseUsed, hby.hzero, hby.hone,
          hbest_j, hu_j, hu_val, hf1, hf2, hf11]
        exact ⟨by wram_simp [dB, heq_e], fun i hi => by wram_simp [hr i hi], by wram_simp⟩
      · have huf : vget used' j = false := Bool.eq_false_iff.mpr hu
        have hu_val : (if vget used' j = true then 1 else 0) = 0 := ite_eq_right hu
        by_cases hlt_r : C (i₀, j) + (-vget s.z j).toNat - (vget s.y i₀).toNat <
            (vget s.minv j).toNat
        · have hlt_z : hgRed c s.y s.z i₀ j < vget s.minv j := by
            rw [hred_eq'] at hlt_r
            omega
          have heq_e : i₀.val = eB (y.regs idx) := by
            simp only [eB, hlt, dite_true]
            change _ = (bestRow' j).val
            simp [bestRow', huf, hlt_z]
          wram_exec [hby.hbaseBestRow, hby.hbaseUsed, hby.hzero, hby.hone, hby.hrn, hby.hbaseC,
            hby.hbaseNZ, hby.hbaseY, hby.hbaseMinv, hri0_y, hbest_j, hu_j, hu_val,
            hC_ij, hnz_j, hy_i, hm_j, hle_sub, hlt_r,
            hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11]
          exact ⟨by wram_simp [dB, heq_e], fun i hi => by wram_simp [hr i hi], by wram_simp⟩
        · have hlt_z : ¬hgRed c s.y s.z i₀ j < vget s.minv j := by
            rw [hred_eq'] at hlt_r
            omega
          have heq_e : (bestRow j).val = eB (y.regs idx) := by
            simp only [eB, hlt, dite_true]
            change _ = (bestRow' j).val
            simp [bestRow', huf, hlt_z]
          wram_exec [hby.hbaseBestRow, hby.hbaseUsed, hby.hzero, hby.hone, hby.hrn, hby.hbaseC,
            hby.hbaseNZ, hby.hbaseY, hby.hbaseMinv, hri0_y, hbest_j, hu_j, hu_val,
            hC_ij, hnz_j, hy_i, hm_j, hle_sub, hlt_r,
            hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11]
          exact ⟨by wram_simp [dB, heq_e], fun i hi => by wram_simp [hr i hi], by wram_simp⟩
    obtain ⟨z, he, hmz, hrz, hiz⟩ := hstep
    obtain ⟨hm', hf'⟩ := prefix_write_step hm hf hmz
    exact ⟨z, he, ⟨hrz, hm', hf'⟩, hiz⟩
  have hexecB : ∃ y₁, ExecWithin w relaxBestRowCode y₀ y₁ (25 * n + 3) ∧
      (∀ i : Fin 28, i.val < 21 → y₁.regs i = x.regs i) ∧
      (∀ j : Fin n, y₁.mem (dB + j.val) = (bestRow' j).val) ∧
      (∀ a, ¬(dB ≤ a ∧ a < dB + n) → y₁.mem a = y₀.mem a) := by
    obtain ⟨y₁, he₁, hr₁, hm₁, hf₁⟩ := exec_forLoop PB
      (fun y hy => (hy.1 rn (by decide)).trans hb.hrn) hbodyB (x := y₀)
      ⟨fun i hi => by wram_simp [hr₀ i hi], fun _ hj => by omega, fun _ _ => rfl⟩
    refine ⟨y₁, he₁.mono (by omega), hr₁, fun j => ?_, hf₁⟩
    simpa [dB, eB, j.isLt] using hm₁ j.val j.isLt
  obtain ⟨y₁, he₁, hr₁, hbest₁, hf₁⟩ := hexecB
  -- Loop 2: relaxMinvCode
  let dM := bC + n * n + 5 * n
  let eM : ℕ → ℕ := fun k =>
    if hk : k < n then (vget (hgExtend c s j₁ i₀).minv ⟨k, hk⟩).toNat else 0
  let PM (k : ℕ) (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ j < k, y.mem (dM + j) = eM j) ∧
      (∀ a, ¬(dM ≤ a ∧ a < dM + k) → y.mem a = y₁.mem a)
  have hbodyM (y : Data 28) (hy : PM (y.regs idx) y) (hlt : y.regs idx < n) :
      ∃ z, ExecWithin w relaxMinvBody y z 21 ∧ PM (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hm, hf⟩ := hy
    let j : Fin n := ⟨y.regs idx, hlt⟩
    have hby : BaseRegs n bC M y := hb.of_eq fun i hi => hr i (by omega)
    have hri0_y : y.regs ri0 = i₀.val := (hr ri0 (by decide)).trans hri0
    have hm_j : y.mem (bC + n * n + 5 * n + y.regs idx) = (vget s.minv j).toNat := by
      rw [hf _ (by simp only [dM]; omega), hf₁ _ (by simp only [dB]; omega),
        hout₀ _ (by omega)]
      exact hSM.hminv j
    have hu_j : y.mem (bC + n * n + 3 * n + y.regs idx) =
        if vget used' j = true then 1 else 0 := by
      rw [hf _ (by simp only [dM]; omega), hf₁ _ (by simp only [dB]; omega)]
      exact hused₀ j
    have hmul : i₀.val * n + y.regs idx < n * n := Cslib.Matrix.pairIndex_lt (i₀, j)
    obtain ⟨hle_sub, hsum_le, hred_eq⟩ := hgRed_nat_eq (hCW i₀ j) (hSI.y_bounds i₀)
      (hSI.z_bounds j) (hSI.feas i₀ j)
    have hC_ij : y.mem (bC + (i₀.val * n + y.regs idx)) = C (i₀, j) := by
      rw [hf _ (by simp only [dM]; omega), hf₁ _ (by simp only [dB]; omega), hout₀ _ (by omega)]
      exact hC i₀ j
    have hnz_j : y.mem (bC + n * n + n + y.regs idx) = (-vget s.z j).toNat := by
      rw [hf _ (by simp only [dM]; omega), hf₁ _ (by simp only [dB]; omega), hout₀ _ (by omega)]
      exact hSM.hnz j
    have hy_i : y.mem (bC + n * n + i₀.val) = (vget s.y i₀).toNat := by
      rw [hf _ (by simp only [dM]; have := i₀.isLt; omega),
        hf₁ _ (by simp only [dB]; have := i₀.isLt; omega),
        hout₀ _ (by have := i₀.isLt; omega)]
      exact hSM.hy i₀
    have hm_nonneg := (hSI.minv_bounds j).1
    have hred_nonneg : 0 ≤ hgRed c s.y s.z i₀ j := hSI.feas i₀ j
    have hred_eq' : C (i₀, j) + (-vget s.z j).toNat - (vget s.y i₀).toNat =
        (hgRed c s.y s.z i₀ j).toNat := hred_eq
    have hf1 : Fits w (dM + y.regs idx) := hfit.of_le (by simp only [dM]; omega)
    have hf2 : Fits w (bC + n * n + 3 * n + y.regs idx) := hfit.of_le (by omega)
    have hf3 : Fits w (i₀.val * n) := hfit.of_le (by omega)
    have hf4 : Fits w (i₀.val * n + y.regs idx) := hfit.of_le (by omega)
    have hf5 : Fits w (bC + (i₀.val * n + y.regs idx)) := hfit.of_le (by omega)
    have hf6 : Fits w (bC + n * n + n + y.regs idx) := hfit.of_le (by omega)
    have hf7 : Fits w (C (i₀, j) + (-vget s.z j).toNat) := hfit.of_le (by omega)
    have hf8 : Fits w (bC + n * n + i₀.val) := hfit.of_le (by have := i₀.isLt; omega)
    have hf9 : Fits w (C (i₀, j) + (-vget s.z j).toNat - (vget s.y i₀).toNat) :=
      hfit.of_le (by omega)
    have hf10 : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    have hminv_ext : vget (hgExtend c s j₁ i₀).minv j =
        if vget used' j = true then vget s.minv j
        else min (vget s.minv j) (hgRed c s.y s.z i₀ j) := by
      simpa only [hgExtend] using hgRelax_minv (c := c) _ i₀ j₁ j
    have hstep : ∃ z, ExecWithin w relaxMinvBody y z 21 ∧
        z.mem = Function.update y.mem (dM + y.regs idx) (eM (y.regs idx)) ∧
        (∀ i : Fin 28, i.val < 21 → z.regs i = x.regs i) ∧
        z.regs idx = y.regs idx + 1 := by
      refine WP.exists_execWithin ?_
      unfold relaxMinvBody
      by_cases hu : vget used' j = true
      · have hu_val : (if vget used' j = true then 1 else 0) = 1 := ite_eq_left hu
        have heq_e : (vget s.minv j).toNat = eM (y.regs idx) := by
          simp only [eM, hlt, dite_true]
          change _ = (vget (hgExtend c s j₁ i₀).minv j).toNat
          rw [hminv_ext, ite_eq_left hu]
        wram_exec [hby.hbaseMinv, hby.hbaseUsed, hby.hzero, hby.hone,
          hm_j, hu_j, hu_val, hf1, hf2, hf10]
        exact ⟨by wram_simp [dM, heq_e], fun i hi => by wram_simp [hr i hi], by wram_simp⟩
      · have hu_val : (if vget used' j = true then 1 else 0) = 0 := ite_eq_right hu
        by_cases hlt_r : C (i₀, j) + (-vget s.z j).toNat - (vget s.y i₀).toNat <
            (vget s.minv j).toNat
        · have heq_e : C (i₀, j) + (-vget s.z j).toNat - (vget s.y i₀).toNat =
              eM (y.regs idx) := by
            simp only [eM, hlt, dite_true]
            change _ = (vget (hgExtend c s j₁ i₀).minv j).toNat
            rw [hminv_ext, ite_eq_right hu, hred_eq']
            simp only [min_def]
            split_ifs <;> omega
          wram_exec [hby.hbaseMinv, hby.hbaseUsed, hby.hzero, hby.hone, hby.hrn, hby.hbaseC,
            hby.hbaseNZ, hby.hbaseY, hri0_y, hm_j, hu_j, hu_val,
            hC_ij, hnz_j, hy_i, hle_sub, hlt_r,
            hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10]
          exact ⟨by wram_simp [dM, heq_e], fun i hi => by wram_simp [hr i hi], by wram_simp⟩
        · have heq_e : (vget s.minv j).toNat = eM (y.regs idx) := by
            simp only [eM, hlt, dite_true]
            change _ = (vget (hgExtend c s j₁ i₀).minv j).toNat
            rw [hminv_ext, ite_eq_right hu]
            rw [hred_eq'] at hlt_r
            simp only [min_def]
            split_ifs <;> omega
          wram_exec [hby.hbaseMinv, hby.hbaseUsed, hby.hzero, hby.hone, hby.hrn, hby.hbaseC,
            hby.hbaseNZ, hby.hbaseY, hri0_y, hm_j, hu_j, hu_val,
            hC_ij, hnz_j, hy_i, hle_sub, hlt_r,
            hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10]
          exact ⟨by wram_simp [dM, heq_e], fun i hi => by wram_simp [hr i hi], by wram_simp⟩
    obtain ⟨z, he, hmz, hrz, hiz⟩ := hstep
    obtain ⟨hm', hf'⟩ := prefix_write_step hm hf hmz
    exact ⟨z, he, ⟨hrz, hm', hf'⟩, hiz⟩
  have hexecM : ∃ y₂, ExecWithin w relaxMinvCode y₁ y₂ (23 * n + 3) ∧
      (∀ i : Fin 28, i.val < 21 → y₂.regs i = x.regs i) ∧
      (∀ j : Fin n, y₂.mem (dM + j.val) = (vget (hgExtend c s j₁ i₀).minv j).toNat) ∧
      (∀ a, ¬(dM ≤ a ∧ a < dM + n) → y₂.mem a = y₁.mem a) := by
    obtain ⟨y₂, he₂, hr₂, hm₂, hf₂⟩ := exec_forLoop PM
      (fun y hy => (hy.1 rn (by decide)).trans hb.hrn) hbodyM (x := y₁)
      ⟨fun i hi => by wram_simp [hr₁ i hi], fun _ hj => by omega, fun _ _ => rfl⟩
    refine ⟨y₂, he₂.mono (by omega), hr₂, fun j => ?_, hf₂⟩
    simpa [dM, eM, j.isLt] using hm₂ j.val j.isLt
  obtain ⟨y₂, he₂, hr₂, hminv₂, hf₂⟩ := hexecM
  have hout : ∀ a, ¬(bC + n * n + 3 * n ≤ a ∧ a < bC + n * n + 7 * n) → y₂.mem a = x.mem a :=
    fun a ha => (hf₂ a (by simp only [dM]; omega)).trans
      ((hf₁ a (by simp only [dB]; omega)).trans (hout₀ a (by omega)))
  refine ⟨y₂, (he₀.seq (he₁.seq he₂)).mono (by omega), hr₂,
    ⟨⟨fun i => ?_, fun j => ?_, fun j => ?_, fun j i hm => ?_, fun i hm => ?_⟩,
      fun j => ?_, fun i => ?_, hminv₂, fun j => ?_⟩,
    fun a ha => hout a (by omega)⟩
  · exact (hout _ (by have := i.isLt; omega)).trans (hSM.hy i)
  · exact (hout _ (by have := j.isLt; omega)).trans (hSM.hnz j)
  · exact (hout _ (by have := j.isLt; omega)).trans (hSM.hcol j)
  · exact (hout _ (by have := i.isLt; omega)).trans (hSM.hrow_some j i hm)
  · exact (hout _ (by have := i.isLt; omega)).trans (hSM.hrow_none i hm)
  · rw [hf₂ _ (by simp only [dM]; have := j.isLt; omega),
      hf₁ _ (by simp only [dB]; have := j.isLt; omega)]
    exact hused₀ j
  · rw [hf₂ _ (by simp only [dM]; have := i.isLt; omega),
      hf₁ _ (by simp only [dB]; have := i.isLt; omega)]
    exact htree₀ i
  · rw [hf₂ _ (by simp only [dM]; have := j.isLt; omega)]
    exact hbest₁ j

/-- Augmenting-path walk body: rematch column `idx2` to `bestRow[idx2]` and advance to its previous
matched column `rowMate[bestRow[idx2]]`. -/
private def augBody : Code .standard 28 := ram[
  addr ← baseBestRow + idx2; val ← *addr;
  addr ← baseRowMate + val; val2 ← *addr;
  addr ← baseColMate + idx2; *addr ← val;
  idx2 ← val2 ]

/-- Apply augmenting path ending at `rj1` to `colMate`. -/
private def augCode : Code .standard 28 :=
  .seq (ram[ idx2 ← rj1 ]) (.loop (.lt idx2 rn) augBody)

/-- Scatter `colMate` into `rowMate` after clearing `rowMate` to `n`. -/
private def scatterRowMateBody : Code .standard 28 := ram[
  addr ← baseColMate + idx; val ← *addr;
  if val < rn then [ addr ← baseRowMate + val; *addr ← idx ] else [ tmp ← zero ];
  idx ← idx + one ]

/-- Rebuild `rowMate` from `colMate` in `O(n)` instructions. -/
private def rebuildRowMateCode : Code .standard 28 :=
  .seq (fillConst baseRowMate rn)
    (.seq (ram[ idx ← #0 ]) (.loop (.lt idx rn) scatterRowMateBody))

/-- Augment matching along `rj1`'s tree path, rebuild `rowMate`, and set `augmented := 1`. -/
private def augmentCode : Code .standard 28 :=
  .seq augCode (.seq rebuildRowMateCode (ram[ augmented ← #1 ]))

private theorem exec_augCode {w n bC M : ℕ} {c : Fin n × Fin n → ℤ} {W : ℕ} {r j₁ : Fin n}
    {s : HgState n} {bestRow : Fin n → Fin n}
    (hSI : HgStepInv c W r s bestRow) (x : Data 28)
    (hb : BaseRegs n bC M x) (hSM : StepMem bC s bestRow x.mem)
    (hrj1 : x.regs rj1 = j₁.val)
    (hfit : Fits w (bC + n * n + 8 * n + 2)) :
    ∃ y, ExecWithin w augCode x y (9 * n + 3) ∧
      (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ j : Fin n, y.mem (bC + n * n + 2 * n + j.val) =
        encodeOptFin (vget (hgApplyEdges s.mate (vget s.path j₁)) j)) ∧
      (∀ a, ¬(bC + n * n + 2 * n ≤ a ∧ a < bC + n * n + 3 * n) → y.mem a = x.mem a) := by
  let dC := bC + n * n + 2 * n
  let I (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ a, ¬(dC ≤ a ∧ a < dC + n) → y.mem a = x.mem a) ∧
      ((y.regs idx2 = n ∧ ∀ j : Fin n, y.mem (dC + j.val) =
          encodeOptFin (vget (hgApplyEdges s.mate (vget s.path j₁)) j)) ∨
       ∃ (j : Fin n) (pref : List (Fin n × Fin n)),
         y.regs idx2 = j.val ∧
         vget s.path j₁ = pref ++ vget s.path j ∧
         ∀ k : Fin n, y.mem (dC + k.val) = encodeOptFin (vget (hgApplyEdges s.mate pref) k))
  let rank (y : Data 28) : ℕ :=
    if h : y.regs idx2 < n then (vget s.path ⟨y.regs idx2, h⟩).length else 0
  have hstepBody (y : Data 28) (hy : I y) (hc : (Cond.lt idx2 rn).Holds y) :
      ∃ z, ExecWithin w augBody y z 7 ∧ I z ∧ rank z < rank y := by
    obtain ⟨hr, hf, hstate⟩ := hy
    have hby : BaseRegs n bC M y := hb.of_eq fun i hi => hr i (by omega)
    have hlt : y.regs idx2 < n := by simpa only [Cond.holds_lt, hby.hrn] using hc
    rcases hstate with ⟨heqn, _⟩ | ⟨j, pref, hj_eq, hpath_eq, hcol_pref⟩
    · omega
    have hj_fin : (⟨y.regs idx2, hlt⟩ : Fin n) = j := Fin.ext hj_eq
    let u := bestRow j
    have hbest_j : y.mem (bC + n * n + 6 * n + y.regs idx2) = u.val := by
      rw [hf _ (by simp only [dC]; omega), hj_eq]
      exact hSM.hbest j
    have hf1 : Fits w (bC + n * n + 6 * n + y.regs idx2) := hfit.of_le (by omega)
    have hf2 : Fits w (bC + n * n + 7 * n + 1 + u.val) := hfit.of_le (by have := u.isLt; omega)
    have hf3 : Fits w (dC + y.regs idx2) := hfit.of_le (by simp only [dC]; omega)
    have hcol_upd : ∀ k : Fin n,
        Function.update y.mem (dC + j.val) u.val (dC + k.val) =
          encodeOptFin (vget (vset (hgApplyEdges s.mate pref) j (some u)) k) := by
      intro k
      by_cases hkj : k = j
      · subst hkj
        simp [encodeOptFin]
      · have hne : dC + k.val ≠ dC + j.val := fun h => hkj (Fin.ext (by omega))
        rw [Function.update_of_ne hne, hcol_pref k, vget_vset_ne _ _ (Ne.symm hkj)]
    by_cases hex : ∃ j' : Fin n, vget s.mate j' = some u
    · obtain ⟨j', hj'⟩ := hex
      have hrow_u : y.mem (bC + n * n + 7 * n + 1 + u.val) = j'.val := by
        rw [hf _ (by simp only [dC]; have := u.isLt; omega)]
        exact hSM.hrow_some j' u hj'
      have hp_cons := hSI.path_eq_cons (j := j) hj'
      have hstep : ∃ z, ExecWithin w augBody y z 7 ∧
          z.mem = Function.update y.mem (dC + j.val) u.val ∧
          (∀ i : Fin 28, i.val < 21 → z.regs i = x.regs i) ∧
          z.regs idx2 = j'.val := by
        refine WP.exists_execWithin ?_
        unfold augBody
        wram_exec [hby.hbaseBestRow, hby.hbaseRowMate, hby.hbaseColMate,
          hbest_j, hrow_u, hf1, hf2, hf3]
        exact ⟨by wram_simp [dC, hj_eq], fun i hi => by wram_simp [hr i hi], by wram_simp⟩
      obtain ⟨z, he, hmz, hrz, hiz⟩ := hstep
      refine ⟨z, he, ⟨hrz, fun a ha => ?_, .inr ⟨j', pref ++ [(u, j)], hiz, ?_, ?_⟩⟩, ?_⟩
      · rw [hmz, Function.update_of_ne (by have := j.isLt; omega)]
        exact hf a ha
      · rw [hpath_eq, hp_cons, List.append_assoc, List.singleton_append]
      · intro k
        rw [hmz, hcol_upd k]
        simp [hgApplyEdges, List.foldl_append]
      · simp only [rank, hlt, hj_fin, hiz, j'.isLt, dite_true, Fin.eta, hp_cons, List.length_cons]
        omega
    · have hfree : ∀ j' : Fin n, vget s.mate j' ≠ some u := fun j' h => hex ⟨j', h⟩
      have hrow_u : y.mem (bC + n * n + 7 * n + 1 + u.val) = n := by
        rw [hf _ (by simp only [dC]; have := u.isLt; omega)]
        exact hSM.hrow_none u hfree
      have hp_sing := hSI.path_eq_singleton (j := j) hfree
      have hstep : ∃ z, ExecWithin w augBody y z 7 ∧
          z.mem = Function.update y.mem (dC + j.val) u.val ∧
          (∀ i : Fin 28, i.val < 21 → z.regs i = x.regs i) ∧
          z.regs idx2 = n := by
        refine WP.exists_execWithin ?_
        unfold augBody
        wram_exec [hby.hbaseBestRow, hby.hbaseRowMate, hby.hbaseColMate,
          hbest_j, hrow_u, hf1, hf2, hf3]
        exact ⟨by wram_simp [dC, hj_eq], fun i hi => by wram_simp [hr i hi], by wram_simp⟩
      obtain ⟨z, he, hmz, hrz, hiz⟩ := hstep
      refine ⟨z, he, ⟨hrz, fun a ha => ?_, .inl ⟨hiz, fun k => ?_⟩⟩, ?_⟩
      · rw [hmz, Function.update_of_ne (by have := j.isLt; omega)]
        exact hf a ha
      · rw [hmz, hcol_upd k, hpath_eq, hp_sing]
        simp only [hgApplyEdges, List.foldl_append, List.foldl_cons, List.foldl_nil]
        rfl
      · simp only [rank, hlt, hj_fin, hiz, lt_self_iff_false, dite_true, dite_false, hp_sing,
          List.length_singleton]
        omega
  have hsetup : ∃ y₀,
      ExecWithin w (ram[ idx2 ← rj1 ] : Code .standard 28) x y₀ 1 ∧ I y₀ ∧ rank y₀ ≤ n := by
    refine WP.exists_execWithin ?_
    wram_exec [hrj1]
    refine ⟨⟨fun i hi => by wram_simp, fun _ _ => rfl,
        .inr ⟨j₁, [], by wram_simp, rfl, fun k => hSM.hcol k⟩⟩, ?_⟩
    simp only [rank]
    have hidx2 : (x.set idx2 j₁.val).regs idx2 = j₁.val := by wram_simp
    rw [dite_eq_left (by rw [hidx2]; exact j₁.isLt)]
    have hfin : (⟨(x.set idx2 j₁.val).regs idx2, by rw [hidx2]; exact j₁.isLt⟩ : Fin n) = j₁ :=
      Fin.ext hidx2
    rw [hfin]
    exact hSI.length_path_le j₁
  obtain ⟨y₀, hs₀, hI₀, hrank₀⟩ := hsetup
  obtain ⟨y, hl, hIy, hcy⟩ := ExecWithin.loop_invariant (cond := .lt idx2 rn) (body := augBody)
    I rank (T := 7) hstepBody hI₀
  obtain ⟨hr, hf, hstate⟩ := hIy
  have hby : BaseRegs n bC M y := hb.of_eq fun i hi => hr i (by omega)
  rcases hstate with ⟨_, hcol_final⟩ | ⟨j, _, hj_eq, _, _⟩
  · refine ⟨y, (hs₀.seq hl).mono ?_, hr, hcol_final,
      fun a ha => hf a (by simp only [dC]; omega)⟩
    have := Nat.mul_le_mul_right 9 hrank₀
    omega
  · simp only [Cond.holds_lt, hj_eq, hby.hrn] at hcy
    exact absurd j.isLt hcy

private theorem exec_rebuildRowMateCode {w n bC M : ℕ} {mate : Vector (Option (Fin n)) n}
    (hM : IsMatching (fun _ => true) (mateMatching mate)) (x : Data 28)
    (hb : BaseRegs n bC M x)
    (hcol : ∀ j : Fin n, x.mem (bC + n * n + 2 * n + j.val) = encodeOptFin (vget mate j))
    (hfit : Fits w (bC + n * n + 8 * n + 2)) :
    ∃ y, ExecWithin w rebuildRowMateCode x y (13 * n + 6) ∧
      (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ j i : Fin n, vget mate j = some i → y.mem (bC + n * n + 7 * n + 1 + i.val) = j.val) ∧
      (∀ i : Fin n, (∀ j : Fin n, vget mate j ≠ some i) →
        y.mem (bC + n * n + 7 * n + 1 + i.val) = n) ∧
      (∀ a, ¬(bC + n * n + 7 * n + 1 ≤ a ∧ a < bC + n * n + 8 * n + 1) → y.mem a = x.mem a) := by
  let bRM := bC + n * n + 7 * n + 1
  obtain ⟨y₁, he₁, hr₁, hrm₁, hf₁⟩ := exec_fillConst baseRowMate rn (by decide) (by decide) x hb
    (by rw [hb.hbaseRowMate]; omega) hfit
  let P (k : ℕ) (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ a, ¬(bRM ≤ a ∧ a < bRM + n) → y.mem a = x.mem a) ∧
      (∀ j : Fin n, j.val < k → ∀ i : Fin n, vget mate j = some i → y.mem (bRM + i.val) = j.val) ∧
      (∀ i : Fin n, (∀ j : Fin n, j.val < k → vget mate j ≠ some i) → y.mem (bRM + i.val) = n)
  have hbody (y : Data 28) (hy : P (y.regs idx) y) (hlt : y.regs idx < n) :
      ∃ z, ExecWithin w scatterRowMateBody y z 6 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hf, hsome, hnone⟩ := hy
    let j₀ : Fin n := ⟨y.regs idx, hlt⟩
    have hby : BaseRegs n bC M y := hb.of_eq fun i hi => hr i (by omega)
    have hcol_j₀ : y.mem (bC + n * n + 2 * n + y.regs idx) = encodeOptFin (vget mate j₀) := by
      rw [hf _ (by simp only [bRM]; omega)]
      exact hcol j₀
    have hf1 : Fits w (bC + n * n + 2 * n + y.regs idx) := hfit.of_le (by omega)
    have hf2 : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    refine WP.exists_execWithin ?_
    unfold scatterRowMateBody
    cases hmj : vget mate j₀ with
    | none =>
      have henc : encodeOptFin (vget mate j₀) = n := by simp [hmj, encodeOptFin]
      wram_exec [hby.hbaseColMate, hby.hrn, hby.hzero, hby.hone, hcol_j₀, henc, hf1, hf2]
      refine ⟨⟨fun i hi => by wram_simp [hr i hi], hf, fun j hj i hm => ?_,
        fun i hall => ?_⟩, by wram_simp⟩
      · by_cases hjj : j = j₀
        · subst hjj; rw [hmj] at hm; cases hm
        · have : j.val ≠ y.regs idx := fun h => hjj (Fin.ext h)
          exact hsome j (by omega) i hm
      · exact hnone i fun j hj => hall j (by omega)
    | some i₀ =>
      have henc : encodeOptFin (vget mate j₀) = i₀.val := by simp [hmj, encodeOptFin]
      have hi₀_lt : i₀.val < n := i₀.isLt
      have hf3 : Fits w (bC + n * n + 7 * n + 1 + i₀.val) := hfit.of_le (by omega)
      wram_exec [hby.hbaseColMate, hby.hbaseRowMate, hby.hrn, hby.hzero, hby.hone,
        hcol_j₀, henc, hi₀_lt, hf1, hf2, hf3]
      refine ⟨⟨fun i hi => by wram_simp [hr i hi], fun a ha => ?_,
        fun j hj i hm => ?_, fun i hall => ?_⟩, by wram_simp⟩
      · change Function.update y.mem (bRM + i₀.val) (y.regs idx) a = x.mem a
        rw [Function.update_of_ne (by omega)]
        exact hf a ha
      · change Function.update y.mem (bRM + i₀.val) (y.regs idx) (bRM + i.val) = j.val
        by_cases hii : i = i₀
        · subst hii
          have hjj : j = j₀ := hM.2.1 i (j) (j₀)
            (mem_mateMatching.mpr hm) (mem_mateMatching.mpr hmj)
          subst hjj
          exact Function.update_self _ _ _
        · have hne : bRM + i.val ≠ bRM + i₀.val := fun h => hii (Fin.ext (by omega))
          have hjj : j ≠ j₀ := fun h => by
            subst h
            rw [hmj] at hm
            exact hii (Option.some.inj hm).symm
          have hj_ne : j.val ≠ y.regs idx := fun h => hjj (Fin.ext h)
          rw [Function.update_of_ne hne]
          exact hsome j (by omega) i hm
      · change Function.update y.mem (bRM + i₀.val) (y.regs idx) (bRM + i.val) = n
        have hii : i ≠ i₀ := fun h => by subst h; exact hall j₀ (Nat.lt_succ_self _) hmj
        have hne : bRM + i.val ≠ bRM + i₀.val := fun h => hii (Fin.ext (by omega))
        rw [Function.update_of_ne hne]
        exact hnone i fun j hj => hall j (by omega)
  obtain ⟨y₃, hl₃, hr₃, hf₃, hsome₃, hnone₃⟩ := exec_forLoop P
    (fun y hy => (hy.1 rn (by decide)).trans hb.hrn) hbody (x := y₁)
    ⟨fun i hi => by wram_simp [hr₁ i hi],
      fun a ha => hf₁ a (by rw [hb.hbaseRowMate]; simp only [bRM] at ha; omega),
      fun _ hj => by omega,
      fun i _ => by
        have := hrm₁ i.val i.isLt
        rwa [hb.hbaseRowMate, hb.hrn] at this⟩
  exact ⟨y₃, (he₁.seq hl₃).mono (by omega), hr₃,
    fun j i hm => hsome₃ j j.isLt i hm,
    fun i hall => hnone₃ i (fun j _ => hall j),
    fun a ha => hf₃ a (by simp only [bRM]; omega)⟩

private theorem exec_augmentCode {w n bC M W : ℕ} {C : Fin n × Fin n → ℕ} {r j₁ : Fin n}
    {s : HgState n} {bestRow : Fin n → Fin n}
    (hSI : HgStepInv (fun p => (C p : ℤ)) W r s bestRow)
    (hj₁ : vget s.used j₁ = false) (hz : vget s.minv j₁ = 0) (hfree : vget s.mate j₁ = none)
    (x : Data 28) (hb : BaseRegs n bC M x) (hSM : StepMem bC s bestRow x.mem)
    (hrj1 : x.regs rj1 = j₁.val)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y, ExecWithin w augmentCode x y (22 * n + 10) ∧
      (∀ i : Fin 28, i.val < 17 → y.regs i = x.regs i) ∧
      y.regs augmented = 1 ∧
      OuterMem bC s.y s.z (hgApplyEdges s.mate (vget s.path j₁)) y.mem ∧
      (∀ a, ¬(bC + n * n + 2 * n ≤ a ∧ a < bC + n * n + 3 * n) ∧
        ¬(bC + n * n + 7 * n + 1 ≤ a ∧ a < bC + n * n + 8 * n + 1) → y.mem a = x.mem a) := by
  have hfit_a : Fits w (bC + n * n + 8 * n + 2) := hfit.of_le (by omega)
  obtain ⟨hOB', _⟩ := hgOuterBound_augment hSI hj₁ hz hfree
  obtain ⟨y₁, he₁, hr₁, hcol₁, hf₁⟩ := exec_augCode hSI x hb hSM hrj1 hfit_a
  have hb₁ : BaseRegs n bC M y₁ := hb.of_eq fun i hi => hr₁ i (by omega)
  obtain ⟨y₂, he₂, hr₂, hsome₂, hnone₂, hf₂⟩ :=
    exec_rebuildRowMateCode hOB'.matching y₁ hb₁ hcol₁ hfit_a
  have hstep₃ : ∃ y₃,
      ExecWithin w (ram[ augmented ← #1 ] : Code .standard 28) y₂ y₃ 1 ∧
      y₃ = y₂.set augmented 1 := by
    refine WP.exists_execWithin ?_
    wram_exec [hfit.of_le (show 1 ≤ _ by omega)]
    rfl
  obtain ⟨y₃, he₃, rfl⟩ := hstep₃
  have hout : ∀ a, ¬(bC + n * n + 2 * n ≤ a ∧ a < bC + n * n + 3 * n) ∧
      ¬(bC + n * n + 7 * n + 1 ≤ a ∧ a < bC + n * n + 8 * n + 1) → y₂.mem a = x.mem a :=
    fun a ⟨ha1, ha2⟩ => (hf₂ a ha2).trans (hf₁ a ha1)
  refine ⟨_, (he₁.seq (he₂.seq he₃)).mono (by omega),
    fun i hi => ?_, by wram_simp,
    ⟨fun i => (hout _ (by have := i.isLt; omega)).trans (hSM.hy i),
     fun j => (hout _ (by have := j.isLt; omega)).trans (hSM.hnz j),
     fun j => (hf₂ _ (by have := j.isLt; omega)).trans (hcol₁ j),
     hsome₂, hnone₂⟩,
    hout⟩
  have h2 := hr₂ i (by omega)
  have h1 := hr₁ i (by omega)
  wram_simp [h2, h1]

/-! ### Phase, core `O(n³)` solver, and full `State.init` wrapper -/

/-- One tree-growing or augmenting round of phase `rr`. -/
private def roundBody : Code .standard 28 :=
  .seq argminCode
    (.seq dualCode
      (.seq (ram[ addr ← baseColMate + rj1; ri0 ← *addr ])
        (ram[ if ri0 = rn then [ ⟪augmentCode⟫ ] else [ ⟪extendCode⟫ ] ])))

/-- Complete alternating-tree phase rooted at free row `rr`. -/
private def phaseCode : Code .standard 28 :=
  .seq initPhaseCode (.loop (.eq augmented zero) roundBody)

private theorem exec_phaseCode {w n bC M W : ℕ} {C : Fin n × Fin n → ℕ}
    {y₀ z₀ : Vector ℤ n} {mate₀ : Vector (Option (Fin n)) n}
    (hCW : ∀ u v, C (u, v) ≤ W)
    (hOB : HgOuterBound (fun p => (C p : ℤ)) W y₀ z₀ mate₀)
    (r : Fin n) (hr_free : r ∉ matchedLeft (mateMatching mate₀))
    (x : Data 28) (hb : BaseRegs n bC M x)
    (hC : CostMem bC C x.mem) (hOM : OuterMem bC y₀ z₀ mate₀ x.mem)
    (hr_reg : x.regs rr = r.val)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y, ExecWithin w phaseCode x y (99 * n * n + 60 * n + 17) ∧
      (∀ i : Fin 28, i.val < 17 → y.regs i = x.regs i) ∧
      HgOuterBound (fun p => (C p : ℤ)) W
        (hgPhase (fun p => (C p : ℤ)) y₀ z₀ mate₀ r).y
        (hgPhase (fun p => (C p : ℤ)) y₀ z₀ mate₀ r).z
        (hgPhase (fun p => (C p : ℤ)) y₀ z₀ mate₀ r).mate ∧
      matchedLeft (mateMatching (hgPhase (fun p => (C p : ℤ)) y₀ z₀ mate₀ r).mate) =
        insert r (matchedLeft (mateMatching mate₀)) ∧
      OuterMem bC
        (hgPhase (fun p => (C p : ℤ)) y₀ z₀ mate₀ r).y
        (hgPhase (fun p => (C p : ℤ)) y₀ z₀ mate₀ r).z
        (hgPhase (fun p => (C p : ℤ)) y₀ z₀ mate₀ r).mate y.mem ∧
      (∀ a, ¬(bC + n * n ≤ a ∧ a < bC + n * n + 8 * n + 1 ∧ a ≠ bC + n * n + 7 * n) →
        y.mem a = x.mem a) := by
  let c : Fin n × Fin n → ℤ := fun p => (C p : ℤ)
  have hc_bounds : ∀ u v, 0 ≤ c (u, v) ∧ c (u, v) ≤ W :=
    fun u v => ⟨Nat.cast_nonneg _, Nat.cast_le.mpr (hCW u v)⟩
  let s_end := hgPhase c y₀ z₀ mate₀ r
  obtain ⟨y_init, he_init, hr_init, haug_init, hSM_init, hf_init⟩ :=
    exec_initPhaseCode hCW hOB r x hb hC hOM hr_reg hfit
  let I (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 17 → y.regs i = x.regs i) ∧
      (∀ a, ¬(bC + n * n ≤ a ∧ a < bC + n * n + 8 * n + 1 ∧ a ≠ bC + n * n + 7 * n) →
        y.mem a = x.mem a) ∧
      ((y.regs augmented = 1 ∧
          HgOuterBound c W s_end.y s_end.z s_end.mate ∧
          matchedLeft (mateMatching s_end.mate) = insert r (matchedLeft (mateMatching mate₀)) ∧
          OuterMem bC s_end.y s_end.z s_end.mate y.mem) ∨
       (y.regs augmented = 0 ∧
          ∃ (s : HgState n) (bestRow : Fin n → Fin n) (fuel : ℕ),
            s.mate = mate₀ ∧
            fuel + usedCount s.used = n ∧
            0 < fuel ∧
            HgStepInv c W r s bestRow ∧
            StepMem bC s bestRow y.mem ∧
            hgLoop c fuel s = s_end))
  let rank (y : Data 28) : ℕ :=
    if y.regs augmented = 0 then
      n - (Finset.univ.filter fun j : Fin n => y.mem (bC + n * n + 3 * n + j.val) = 1).card
    else 0
  have hused_card_eq : ∀ {s : HgState n} {bestRow : Fin n → Fin n} {m : ℕ → ℕ},
      StepMem bC s bestRow m →
      (Finset.univ.filter fun j : Fin n => m (bC + n * n + 3 * n + j.val) = 1).card =
        usedCount s.used := by
    intro s bestRow m hSM
    unfold usedCount
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hSM.hused j]
    cases vget s.used j <;> simp
  have hstepRound (y : Data 28) (hy : I y) (hc : (Cond.eq augmented zero).Holds y) :
      ∃ z, ExecWithin w roundBody y z (94 * n + 28) ∧ I z ∧ rank z < rank y := by
    obtain ⟨hr, hf, hstate⟩ := hy
    have hby : BaseRegs n bC M y := hb.of_eq fun i hi => hr i (by omega)
    have haug0 : y.regs augmented = 0 := by simpa only [Cond.holds_eq, hby.hzero] using hc
    rcases hstate with ⟨h1, _⟩ |
        ⟨_, s, bestRow, fuel, hs_mate, hfuel_eq, hfuel_pos, hSI, hSM, hloop_eq⟩
    · omega
    obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hfuel_pos)
    have hCy : CostMem bC C y.mem := hC.of_outside fun a ha => hf a (by omega)
    obtain ⟨y₁, j₁, he₁, hr₁, hmem₁, harg, hrj1₁, hrdel₁⟩ := exec_argminCode hSI y hby hSM hfit
    obtain ⟨hj₁_unused, hmin⟩ := hgArgmin_some harg
    have hb₁ : BaseRegs n bC M y₁ := hby.of_eq fun i hi => hr₁ i (by omega)
    have hSM₁ : StepMem bC s bestRow y₁.mem := hmem₁ ▸ hSM
    obtain ⟨y₂, he₂, hr₂, hSM₂, hf₂⟩ :=
      exec_dualCode hCW hSI hj₁_unused hmin y₁ hb₁ hSM₁ hrdel₁ hfit
    have hSD := hgStepInv_dual hc_bounds hSI hj₁_unused hmin
    have hz_j₁ : vget (hgDual s (vget s.minv j₁)).minv j₁ = 0 := by
      rw [hgDual_minv, hj₁_unused, ite_eq_right Bool.false_ne_true, sub_self]
    have hb₂ : BaseRegs n bC M y₂ := hb₁.of_eq fun i hi => hr₂ i (by omega)
    have hrj1₂ : y₂.regs rj1 = j₁.val := (hr₂ rj1 (by decide)).trans hrj1₁
    have hf_cm : Fits w (bC + n * n + 2 * n + j₁.val) := hfit.of_le (by have := j₁.isLt; omega)
    have hcm_j₁ : y₂.mem (bC + n * n + 2 * n + j₁.val) = encodeOptFin (vget s.mate j₁) := by
      simpa only [hgDual_mate] using hSM₂.hcol j₁
    have hstep₃ : ∃ y₃, ExecWithin w (ram[ addr ← baseColMate + rj1; ri0 ← *addr ]) y₂ y₃ 2 ∧
        (∀ i : Fin 28, i.val < 20 → y₃.regs i = y₂.regs i) ∧
        y₃.mem = y₂.mem ∧
        y₃.regs ri0 = encodeOptFin (vget s.mate j₁) := by
      refine WP.exists_execWithin ?_
      wram_exec [hb₂.hbaseColMate, hrj1₂, hcm_j₁, hf_cm]
      exact ⟨fun i hi => by wram_simp, rfl, by wram_simp⟩
    obtain ⟨y₃, he₃, hr₃, hmem₃, hri0₃⟩ := hstep₃
    have hb₃ : BaseRegs n bC M y₃ := hb₂.of_eq fun i hi => hr₃ i (by omega)
    have hrj1₃ : y₃.regs rj1 = j₁.val := (hr₃ rj1 (by decide)).trans hrj1₂
    have hSM₃ : StepMem bC (hgDual s (vget s.minv j₁)) bestRow y₃.mem := hmem₃ ▸ hSM₂
    have hout₃ : ∀ a, ¬(bC + n * n ≤ a ∧ a < bC + n * n + 8 * n + 1 ∧ a ≠ bC + n * n + 7 * n) →
        y₃.mem a = x.mem a := by
      intro a ha
      rw [hmem₃, hf₂ a (by omega), hmem₁]
      exact hf a ha
    cases hm : vget s.mate j₁ with
    | none =>
      have hri0_n : y₃.regs ri0 = n := by simpa [hm, encodeOptFin] using hri0₃
      have hmate_d : vget (hgDual s (vget s.minv j₁)).mate j₁ = none := by
        simpa only [hgDual_mate] using hm
      obtain ⟨hOB', hL'⟩ := hgOuterBound_augment hSD hj₁_unused hz_j₁ hmate_d
      obtain ⟨y₄, he₄, hr₄, haug₄, hOM₄, hf₄⟩ :=
        exec_augmentCode hSD hj₁_unused hz_j₁ hmate_d y₃ hb₃ hSM₃ hrj1₃ hfit
      have hbr : ExecWithin w (ram[ if ri0 = rn then [ ⟪augmentCode⟫ ] else [ ⟪extendCode⟫ ] ])
          y₃ y₄ (22 * n + 11) := by
        obtain ⟨t, ht, hex⟩ := he₄
        exact ⟨t + 1, by omega, .branch_pos (by simp [Cond.holds_eq, hri0_n, hb₃.hrn]) hex⟩
      have hsend : { (hgDual s (vget s.minv j₁)) with
          mate := hgApplyEdges (hgDual s (vget s.minv j₁)).mate
            (vget (hgDual s (vget s.minv j₁)).path j₁) } = s_end := by
        rw [← hloop_eq]
        simp [hgLoop, harg, hm]
      refine ⟨y₄, (he₁.seq (he₂.seq (he₃.seq hbr))).mono (by omega),
        ⟨fun i hi => ?_, fun a ha => (hf₄ a (by omega)).trans (hout₃ a ha),
          .inl ⟨haug₄, ?_, ?_, ?_⟩⟩, ?_⟩
      · exact ((((hr₄ i hi).trans (hr₃ i (by omega))).trans (hr₂ i (by omega))).trans
          (hr₁ i (by omega))).trans (hr i hi)
      · simpa only [← hsend] using hOB'
      · rw [← hsend]
        simpa only [hgDual_mate, hs_mate] using hL'
      · simpa only [← hsend] using hOM₄
      · simp only [rank, haug0, haug₄, one_ne_zero, ↓reduceIte, hused_card_eq hSM]
        omega
    | some i₀ =>
      have hri0_i : y₃.regs ri0 = i₀.val := by simpa [hm, encodeOptFin] using hri0₃
      have hri0_ne : y₃.regs ri0 ≠ n := by rw [hri0_i]; exact ne_of_lt i₀.isLt
      have hmate_d : vget (hgDual s (vget s.minv j₁)).mate j₁ = some i₀ := by
        simpa only [hgDual_mate] using hm
      have hSE := hgStepInv_extend hc_bounds hSD hj₁_unused hz_j₁ hmate_d
      have hC₃ : CostMem bC C y₃.mem := hC.of_outside fun a ha => hout₃ a (by omega)
      obtain ⟨y₄, he₄, hr₄, hSM₄, hf₄⟩ :=
        exec_extendCode hCW hSD y₃ hb₃ hC₃ hSM₃ hrj1₃ hri0_i hfit
      have hbr : ExecWithin w (ram[ if ri0 = rn then [ ⟪augmentCode⟫ ] else [ ⟪extendCode⟫ ] ])
          y₃ y₄ (48 * n + 12) := by
        obtain ⟨t, ht, hex⟩ := he₄
        exact ⟨t + 2, by omega, .branch_neg (by simp [Cond.holds_eq, hri0_ne, hb₃.hrn]) hex⟩
      have haug₄ : y₄.regs augmented = 0 :=
        ((((hr₄ augmented (by decide)).trans (hr₃ augmented (by decide))).trans
          (hr₂ augmented (by decide))).trans (hr₁ augmented (by decide))).trans haug0
      have hcnt' : usedCount (hgExtend c (hgDual s (vget s.minv j₁)) j₁ i₀).used =
          usedCount s.used + 1 := by
        rw [hgExtend_used, hgDual_used]
        exact usedCount_vset hj₁_unused
      have hfuel'_eq :
          fuel' + usedCount (hgExtend c (hgDual s (vget s.minv j₁)) j₁ i₀).used = n := by
        omega
      have hfuel'_pos : 0 < fuel' := by
        have h1 := usedCount_le hSE.matching hSE.used_mate
        have h2 := card_lt_of_root_free hSE.matching hSE.root_free
        omega
      have hloop'_eq : hgLoop c fuel' (hgExtend c (hgDual s (vget s.minv j₁)) j₁ i₀) = s_end := by
        rw [← hloop_eq]
        simp [hgLoop, harg, hm]
      refine ⟨y₄, (he₁.seq (he₂.seq (he₃.seq hbr))).mono (by omega),
        ⟨fun i hi => ?_, fun a ha => (hf₄ a (by omega)).trans (hout₃ a ha),
          .inr ⟨haug₄, _, _, fuel', by rw [hgExtend_mate, hgDual_mate, hs_mate],
            hfuel'_eq, hfuel'_pos, hSE, hSM₄, hloop'_eq⟩⟩, ?_⟩
      · exact ((((hr₄ i (by omega)).trans (hr₃ i (by omega))).trans (hr₂ i (by omega))).trans
          (hr₁ i (by omega))).trans (hr i hi)
      · simp only [rank, haug0, haug₄, ↓reduceIte, hused_card_eq hSM, hused_card_eq hSM₄]
        rw [hcnt']
        omega
  have hI_init : I y_init := by
    have hcnt0 : usedCount (hgInit c y₀ z₀ mate₀ r).used = 0 := by
      unfold usedCount
      simp [hgInit_used]
    refine ⟨hr_init, fun a ha => hf_init a (by omega),
      .inr ⟨haug_init, hgInit c y₀ z₀ mate₀ r, fun _ => r, n, rfl, by omega, r.pos,
        hgStepInv_init hc_bounds hOB hr_free, hSM_init, rfl⟩⟩
  have hrank_init : rank y_init ≤ n := by
    simp only [rank]
    split_ifs
    omega
  obtain ⟨y, hl, hIy, hcy⟩ := ExecWithin.loop_invariant
    (cond := .eq augmented zero) (body := roundBody) I rank (T := 94 * n + 28) hstepRound hI_init
  obtain ⟨hr, hf, hstate⟩ := hIy
  have hby : BaseRegs n bC M y := hb.of_eq fun i hi => hr i (by omega)
  rcases hstate with ⟨_, hOB_end, hL_end, hOM_end⟩ | ⟨haug0, _⟩
  · refine ⟨y, (he_init.seq hl).mono ?_, hr, hOB_end, hL_end, hOM_end, hf⟩
    have := Nat.mul_le_mul_right (94 * n + 28 + 2) hrank_init
    nlinarith
  · exact absurd (Cond.holds_eq.mpr (haug0.trans hby.hzero.symm)) hcy

/-- Run `phaseCode` and increment `rr`. -/
private def phasesBody : Code .standard 28 :=
  .seq phaseCode (ram[ rr ← rr + one ])

/-- Run all `n` alternating-tree phases (`rr = 0 .. n - 1`). -/
private def phasesCode : Code .standard 28 :=
  .seq (ram[ rr ← #0 ]) (.loop (.lt rr rn) phasesBody)

private theorem hgRows_append_singleton {n : ℕ} (c : Fin n × Fin n → ℤ)
    (rs : List (Fin n)) (r : Fin n) (s : HgState n) :
    hgRows c (rs ++ [r]) s =
      hgPhase c (hgRows c rs s).y (hgRows c rs s).z (hgRows c rs s).mate r := by
  induction rs generalizing s with
  | nil => rfl
  | cons a rs ih => exact ih (hgPhase c s.y s.z s.mate a)

/-- Instruction bound for `coreCode` (`O(n³)`). -/
@[expose] def coreTime (n : ℕ) : ℕ :=
  99 * n ^ 3 + 70 * n ^ 2 + 48 * n + 16

/-- Core `O(n³)` Hungarian solver on an in-memory `n × n` unsigned cost matrix `C` at `baseC`:
initializes row potentials `y`, column potentials `nz`, and mates, runs `n` augmenting phases, and
writes length `n` at `outBase`. -/
def coreCode : Code .standard 28 :=
  .seq initOuterCode (.seq phasesCode (ram[ *outBase ← rn ]))

/-- **`O(n³)` Word-RAM execution on an in-memory unsigned/shifted cost matrix.** Given `BaseRegs`
and `CostMem` for an `n × n` matrix `C : Fin n × Fin n → ℕ` bounded by `W` at `bC`, `coreCode`
halts within `coreTime n = O(n³)` instructions at every word width satisfying
`Fits w (bC + n * n + 8 * n + 2 * W + 2)`, leaving `(hungarian fun p => (C p : ℤ))`'s potentials
and perfect matching in memory. -/
theorem core_exec {w n bC M W : ℕ} {C : Fin n × Fin n → ℕ}
    (hCW : ∀ u v, C (u, v) ≤ W) (x : Data 28)
    (hb : BaseRegs n bC M x) (hC : CostMem bC C x.mem)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    let c : Fin n × Fin n → ℤ := fun p => (C p : ℤ)
    let out := hungarian c
    ∃ y, ExecWithin w coreCode x y (coreTime n) ∧
      (∀ i : Fin 28, i.val < 16 → y.regs i = x.regs i) ∧
      (∀ u : Fin n, (y.mem (bC + n * n + u.val) : ℤ) = out.y u) ∧
      (∀ v : Fin n, -(y.mem (bC + n * n + n + v.val) : ℤ) = out.z v) ∧
      y.mem (bC + n * n + 7 * n) = n ∧
      (∀ u : Fin n, ∃ v : Fin n, y.mem (bC + n * n + 7 * n + 1 + u.val) = v.val ∧
        (u, v) ∈ out.matching) ∧
      (∀ a, a < bC + n * n ∨ bC + n * n + 8 * n + 1 ≤ a → y.mem a = x.mem a) := by
  intro c out
  have hc_bounds : ∀ u v, 0 ≤ c (u, v) ∧ c (u, v) ≤ W :=
    fun u v => ⟨Nat.cast_nonneg _, Nat.cast_le.mpr (hCW u v)⟩
  obtain ⟨y₁, he₁, hr₁, hOM₁, hf₁⟩ := exec_initOuterCode hCW x hb hC hfit
  let s₀ := hgStartState (Vector.ofFn (hgRowMin c)) (Vector.replicate n 0) (Vector.replicate n none)
  let sAt (k : ℕ) : HgState n := hgRows c ((List.finRange n).take k) s₀
  let P (k : ℕ) (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 16 → y.regs i = x.regs i) ∧
      HgOuterBound c W (sAt k).y (sAt k).z (sAt k).mate ∧
      matchedLeft (mateMatching (sAt k).mate) = ((List.finRange n).take k).toFinset ∧
      OuterMem bC (sAt k).y (sAt k).z (sAt k).mate y.mem ∧
      (∀ a, ¬(bC + n * n ≤ a ∧ a < bC + n * n + 8 * n + 1 ∧ a ≠ bC + n * n + 7 * n) →
        y.mem a = x.mem a)
  have hbody (y : Data 28) (hy : P (y.regs rr) y) (hlt : y.regs rr < n) :
      ∃ z, ExecWithin w phasesBody y z (99 * n * n + 60 * n + 18) ∧
        P (y.regs rr + 1) z ∧ z.regs rr = y.regs rr + 1 := by
    obtain ⟨hr, hOB_k, hL_k, hOM_k, hf_k⟩ := hy
    let r : Fin n := ⟨y.regs rr, hlt⟩
    have hby : BaseRegs n bC M y := hb.of_eq hr
    have hCy : CostMem bC C y.mem := hC.of_outside fun a ha => hf_k a (by omega)
    have hr_free : r ∉ matchedLeft (mateMatching (sAt (y.regs rr)).mate) := by
      rw [hL_k, List.mem_toFinset]
      intro hmem
      obtain ⟨idx_m, hlt_m, heq_m⟩ := List.mem_iff_getElem.mp hmem
      rw [List.getElem_take, List.getElem_finRange] at heq_m
      have h1 : idx_m < y.regs rr := by
        rw [List.length_take] at hlt_m
        omega
      have h2 : idx_m = y.regs rr := congrArg Fin.val heq_m
      omega
    obtain ⟨y_p, he_p, hr_p, hOB_p, hL_p, hOM_p, hf_p⟩ :=
      exec_phaseCode hCW hOB_k r hr_free y hby hCy hOM_k rfl hfit
    have hrr_p : y_p.regs rr = y.regs rr := hr_p rr (by decide)
    have hone_p : y_p.regs one = 1 := (hr_p one (by decide)).trans hby.hone
    have hf_next : Fits w (y.regs rr + 1) := hfit.of_le (by omega)
    have hstep_inc : ∃ z,
        ExecWithin w (ram[ rr ← rr + one ] : Code .standard 28) y_p z 1 ∧
        z = y_p.set rr (y.regs rr + 1) := by
      refine WP.exists_execWithin ?_
      wram_exec [hrr_p, hone_p, hf_next]
      rfl
    obtain ⟨z, he_inc, rfl⟩ := hstep_inc
    have hs_succ : sAt (y.regs rr + 1) =
        hgPhase c (sAt (y.regs rr)).y (sAt (y.regs rr)).z (sAt (y.regs rr)).mate r := by
      simp only [sAt, List.take_succ_finRange hlt, hgRows_append_singleton]
      rfl
    refine ⟨_, (he_p.seq he_inc).mono (by omega), ⟨fun i hi => ?_, ?_, ?_, ?_, ?_⟩, by wram_simp⟩
    · have hp := hr_p i (by omega)
      wram_simp [hp, hr i hi]
    · rwa [hs_succ]
    · rw [hs_succ, hL_p, hL_k, List.take_succ_finRange hlt]
      dsimp only [r]
      ext u
      simp
    · change OuterMem bC _ _ _ y_p.mem
      rwa [hs_succ]
    · intro a ha
      exact (hf_p a ha).trans (hf_k a ha)
  have hL0 : matchedLeft (mateMatching (Vector.replicate n (none : Option (Fin n)))) = ∅ := by
    ext u
    simp [mem_matchedLeft, mem_mateMatching, vget_replicate]
  obtain ⟨y₃, hl₃, hr₃, hOB_n, hL_n, hOM_n, hf₃⟩ := exec_forLoop P
    (fun y hy => (hy.1 rn (by decide)).trans hb.hrn) hbody (x := y₁)
    ⟨fun i hi => by wram_simp [hr₁ i (by omega)],
      hgOuterBound_start hc_bounds, hL0, hOM₁, hf₁⟩
  have hb₃ : BaseRegs n bC M y₃ := hb.of_eq hr₃
  have hf_out : Fits w (bC + n * n + 7 * n) := hfit.of_le (by omega)
  have hstep₄ : ∃ y₄,
      ExecWithin w (ram[ *outBase ← rn ] : Code .standard 28) y₃ y₄ 1 ∧
      y₄ = y₃.write (bC + n * n + 7 * n) n := by
    refine WP.exists_execWithin ?_
    wram_exec [hb₃.houtBase, hb₃.hrn, hf_out]
    rfl
  obtain ⟨y₄, he₄, rfl⟩ := hstep₄
  have hs_n : sAt n = hgRows c (List.finRange n) s₀ := by
    simp [sAt, List.take_of_length_le (show (List.finRange n).length ≤ n by simp)]
  have hL_univ : matchedLeft (mateMatching (hgRows c (List.finRange n) s₀).mate) = Finset.univ := by
    rw [← hs_n, hL_n, List.take_of_length_le (show (List.finRange n).length ≤ n by simp)]
    ext u
    simp
  have hm_eq : out.matching = mateMatching (hgRows c (List.finRange n) s₀).mate := by
    ext ⟨u, v⟩
    simp [out, hungarian, s₀, mem_foldl_hkMatchingStep, mem_mateMatching]
  refine ⟨_, (he₁.seq (hl₃.seq he₄)).mono ?_, hr₃,
    fun u => ?_, fun v => ?_, by simp, fun u => ?_, fun a ha => ?_⟩
  · unfold coreTime
    nlinarith
  · change (Function.update y₃.mem (bC + n * n + 7 * n) n (bC + n * n + u.val) : ℤ) = _
    rw [Function.update_of_ne (by have := u.isLt; omega), hOM_n.hy u, hs_n]
    have hy_nonneg := (hs_n ▸ hOB_n).y_bounds u
    change ((vget (hgRows c (List.finRange n) s₀).y u).toNat : ℤ) =
      vget (hgRows c (List.finRange n) s₀).y u
    omega
  · change -(Function.update y₃.mem (bC + n * n + 7 * n) n (bC + n * n + n + v.val) : ℤ) = _
    rw [Function.update_of_ne (by have := v.isLt; omega), hOM_n.hnz v, hs_n]
    have hz_nonpos := (hs_n ▸ hOB_n).z_bounds v
    change -((-vget (hgRows c (List.finRange n) s₀).z v).toNat : ℤ) =
      vget (hgRows c (List.finRange n) s₀).z v
    omega
  · have hu_mem : u ∈ matchedLeft (mateMatching (sAt n).mate) := by
      rw [hs_n, hL_univ]
      exact Finset.mem_univ u
    obtain ⟨v, hv⟩ := mem_matchedLeft.mp hu_mem
    have hmv : vget (sAt n).mate v = some u := mem_mateMatching.mp hv
    refine ⟨v, ?_, ?_⟩
    · change Function.update y₃.mem (bC + n * n + 7 * n) n (bC + n * n + 7 * n + 1 + u.val) = v.val
      rw [Function.update_of_ne (by omega)]
      exact hOM_n.hrow_some v u hmv
    · rw [hm_eq, ← hs_n]
      exact hv
  · change Function.update y₃.mem (bC + n * n + 7 * n) n a = x.mem a
    rw [Function.update_of_ne (by omega)]
    exact hf₃ a (by omega)

/-! ### Full `State.init` signed-integer program -/

/-- Read `n = mem[1]` and set up all constants and array bases starting at `baseC = 2 + n * n`. -/
private def setupCode : Code .standard 28 := ram[
  zero ← #0; one ← #1; two ← #2;
  rn ← *one; rnn ← rn * rn; rM ← #0;
  baseC ← two + rnn;
  baseY ← baseC + rnn;
  baseNZ ← baseY + rn;
  baseColMate ← baseNZ + rn;
  baseUsed ← baseColMate + rn;
  baseTree ← baseUsed + rn;
  baseMinv ← baseTree + rn;
  baseBestRow ← baseMinv + rn;
  outBase ← baseBestRow + rn;
  baseRowMate ← outBase + one ]

/-- Scan input words `2 .. 2 + n² - 1` for `rM = max |cost|`. -/
private def scanMaxBody : Code .standard 28 := ram[
  addr ← two + idx; val ← *addr; val ← val / two;
  if rM < val then [ rM ← val ] else [ tmp ← zero ];
  idx ← idx + one ]

/-- Compute `rM` across all `n²` encoded entries. -/
private def scanMaxCode : Code .standard 28 :=
  .seq (ram[ rM ← #0; idx ← #0 ]) (.loop (.lt idx rnn) scanMaxBody)

/-- Decode `Signed.encode` word `2 + idx` and store shifted cost `(cost + rM).toNat` at
`baseC + idx`. -/
private def fillCBody : Code .standard 28 := ram[
  addr ← two + idx; val ← *addr;
  val2 ← val / two; tmp ← val % two;
  if tmp = zero then [ val ← rM + val2 ] else [ val ← rM - val2 ];
  addr ← baseC + idx; *addr ← val; idx ← idx + one ]

/-- Populate `[baseC, baseC + n²)` with nonnegative shifted costs. -/
private def fillCCode : Code .standard 28 :=
  .seq (ram[ idx ← #0 ]) (.loop (.lt idx rnn) fillCBody)

/-- Accumulate `C[idx, rowMate[idx]]` into `acc`. -/
private def sumCostBody : Code .standard 28 := ram[
  addr ← baseRowMate + idx; val ← *addr;
  addr ← idx * rn; addr ← addr + val; addr ← baseC + addr; val ← *addr;
  acc ← acc + val; idx ← idx + one ]

/-- Compute `Signed.encode` of the optimal unshifted matching cost into `acc`. -/
private def sumCostCode : Code .standard 28 :=
  .seq (ram[ acc ← #0; idx ← #0 ])
    (.seq (.loop (.lt idx rn) sumCostBody)
      (ram[ val ← rn * rM;
            if acc < val then [
              val2 ← val - acc; acc ← two * val2; acc ← acc + one
            ] else [
              val2 ← acc - val; acc ← two * val2 ] ]))

/-- Complete structured Hungarian algorithm from `Data.init inst.encode`: computes both
`outputList mem outBase = inst.assignment` and `regs acc = inst.encodedMinCost`. -/
def inputCode : Code .standard 28 :=
  .seq setupCode (.seq scanMaxCode (.seq fillCCode (.seq coreCode sumCostCode)))

/-- Fixed standard-basis Word-RAM program returning the optimal assignment list via
`ExecutesList`. -/
def assignmentProgram : Program .standard 28 := inputCode.program outBase

/-- Fixed standard-basis Word-RAM program returning `Signed.encode` of the minimum matching cost. -/
def minCostProgram : Program .standard 28 := inputCode.program acc

/-- Total instruction bound (including the final `halt`) for `assignmentProgram` and
`minCostProgram`: `99 n³ + 91 n² + 58 n + 52 = O(n³)`. -/
@[expose] def hungarianTime (n : ℕ) : ℕ :=
  99 * n ^ 3 + 91 * n ^ 2 + 58 * n + 52

private theorem exec_setupCode {w : ℕ} (inst : Instance) (hw : Fits w inst.wordBound) :
    ∃ y₁, ExecWithin w setupCode (Data.init inst.encode) y₁ 16 ∧
      BaseRegs inst.n (2 + inst.n * inst.n) 0 y₁ ∧
      y₁.mem = (Data.init inst.encode : Data 28).mem := by
  have hmem1 : (Data.init inst.encode : Data 28).mem 1 = inst.n := inst.init_mem_n
  have hf1 : Fits w 1 := hw.of_le (by unfold Instance.wordBound; omega)
  have hf2 : Fits w 2 := hw.of_le (by unfold Instance.wordBound; omega)
  have hf_nn : Fits w (inst.n * inst.n) := hw.of_le (by unfold Instance.wordBound; nlinarith)
  have hf_bC : Fits w (2 + inst.n * inst.n) := hw.of_le (by unfold Instance.wordBound; nlinarith)
  have hf_bY : Fits w (2 + inst.n * inst.n + inst.n * inst.n) :=
    hw.of_le (by unfold Instance.wordBound; nlinarith)
  have hf_bNZ : Fits w (2 + inst.n * inst.n + inst.n * inst.n + inst.n) :=
    hw.of_le (by unfold Instance.wordBound; nlinarith)
  have hf_bCM : Fits w (2 + inst.n * inst.n + inst.n * inst.n + inst.n + inst.n) :=
    hw.of_le (by unfold Instance.wordBound; nlinarith)
  have hf_bU : Fits w (2 + inst.n * inst.n + inst.n * inst.n + inst.n + inst.n + inst.n) :=
    hw.of_le (by unfold Instance.wordBound; nlinarith)
  have hf_bT :
      Fits w (2 + inst.n * inst.n + inst.n * inst.n + inst.n + inst.n + inst.n + inst.n) :=
    hw.of_le (by unfold Instance.wordBound; nlinarith)
  have hf_bM : Fits w
      (2 + inst.n * inst.n + inst.n * inst.n + inst.n + inst.n + inst.n + inst.n + inst.n) :=
    hw.of_le (by unfold Instance.wordBound; nlinarith)
  have hf_bB : Fits w (2 + inst.n * inst.n + inst.n * inst.n + inst.n + inst.n + inst.n +
      inst.n + inst.n + inst.n) :=
    hw.of_le (by unfold Instance.wordBound; nlinarith)
  have hf_out : Fits w (2 + inst.n * inst.n + inst.n * inst.n + inst.n + inst.n + inst.n +
      inst.n + inst.n + inst.n + inst.n) :=
    hw.of_le (by unfold Instance.wordBound; nlinarith)
  have hf_bRM : Fits w (2 + inst.n * inst.n + inst.n * inst.n + inst.n + inst.n + inst.n +
      inst.n + inst.n + inst.n + inst.n + 1) :=
    hw.of_le (by unfold Instance.wordBound; nlinarith)
  refine WP.exists_execWithin ?_
  unfold setupCode
  wram_exec [hmem1, hf1, hf2, hf_nn, hf_bC, hf_bY, hf_bNZ, hf_bCM, hf_bU, hf_bT, hf_bM,
    hf_bB, hf_out, hf_bRM]
  refine ⟨?_, rfl⟩
  exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
    by wram_simp, by wram_simp, by wram_simp, by wram_simp; omega,
    by wram_simp; omega, by wram_simp; omega, by wram_simp; omega,
    by wram_simp; omega, by wram_simp; omega, by wram_simp; omega⟩

private theorem exec_scanMaxCode {w : ℕ} (inst : Instance) (hw : Fits w inst.wordBound)
    (y₁ : Data 28) (hb₁ : BaseRegs inst.n (2 + inst.n * inst.n) 0 y₁)
    (hmem₁ : y₁.mem = (Data.init inst.encode : Data 28).mem) :
    ∃ y₂, ExecWithin w scanMaxCode y₁ y₂ (9 * inst.n * inst.n + 4) ∧
      BaseRegs inst.n (2 + inst.n * inst.n) (y₂.regs rM) y₂ ∧
      y₂.mem = (Data.init inst.encode : Data 28).mem ∧
      y₂.regs rM ≤ inst.maxMag ∧
      (∀ u v : Fin inst.n, (inst.cost (u, v)).natAbs ≤ y₂.regs rM) := by
  let n := inst.n
  let bC := 2 + n * n
  let x₀ : Data 28 := Data.init inst.encode
  let PM (k : ℕ) (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 16 → i ≠ rM → y.regs i = y₁.regs i) ∧
      y.mem = x₀.mem ∧
      y.regs rM ≤ inst.maxMag ∧
      (∀ q : ℕ, (hq : q < k) → (hq' : q < n * n) →
        (inst.cost (finProdFinEquiv.symm ⟨q, hq'⟩)).natAbs ≤ y.regs rM)
  have hbodyM (y : Data 28) (hy : PM (y.regs idx) y) (hlt : y.regs idx < n * n) :
      ∃ z, ExecWithin w scanMaxBody y z 7 ∧ PM (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hmem, hM_le, hM_ge⟩ := hy
    let p := finProdFinEquiv.symm ⟨y.regs idx, hlt⟩
    let u := p.1
    let v := p.2
    have hp_mul : u.val * n + v.val = y.regs idx :=
      (Cslib.Matrix.pairIndex_eq_val_finProdFinEquiv p).trans
        (congrArg Fin.val (finProdFinEquiv.apply_symm_apply ⟨y.regs idx, hlt⟩))
    have htwo_y : y.regs two = 2 := (hr two (by decide) (by decide)).trans hb₁.htwo
    have hzero_y : y.regs zero = 0 := (hr zero (by decide) (by decide)).trans hb₁.hzero
    have hone_y : y.regs one = 1 := (hr one (by decide) (by decide)).trans hb₁.hone
    have hload : y.mem (2 + y.regs idx) = Signed.encode (inst.cost (u, v)) := by
      rw [hmem, ← hp_mul]
      exact inst.init_mem_cost u v
    have hdiv : Signed.encode (inst.cost (u, v)) / 2 = (inst.cost (u, v)).natAbs :=
      Signed.encode_div_two _
    have hmag_le : (inst.cost (u, v)).natAbs ≤ inst.maxMag := inst.natAbs_cost_le_maxMag u v
    have hf1 : Fits w (2 + y.regs idx) :=
      hw.of_le (by unfold Instance.wordBound; simp only [n] at hlt; nlinarith)
    have hf2 : Fits w ((inst.cost (u, v)).natAbs) :=
      hw.of_le (by unfold Instance.wordBound; nlinarith)
    have hf3 : Fits w (y.regs idx + 1) :=
      hw.of_le (by unfold Instance.wordBound; simp only [n] at hlt; nlinarith)
    refine WP.exists_execWithin ?_
    unfold scanMaxBody
    by_cases hcmp : y.regs rM < (inst.cost (u, v)).natAbs
    · wram_exec [htwo_y, hzero_y, hone_y, hload, hdiv, hcmp, hf1, hf2, hf3]
      refine ⟨⟨fun i hi hne => by wram_simp [hr i hi hne], hmem,
        by wram_simp; exact hmag_le, fun q hq hq' => ?_⟩, by wram_simp⟩
      wram_simp
      rcases eq_or_ne q (y.regs idx) with rfl | hne
      · exact le_rfl
      · exact (hM_ge q (by omega) hq').trans (le_of_lt hcmp)
    · wram_exec [htwo_y, hzero_y, hone_y, hload, hdiv, hcmp, hf1, hf2, hf3]
      refine ⟨⟨fun i hi hne => by wram_simp [hr i hi hne], hmem,
        by wram_simp; exact hM_le, fun q hq hq' => ?_⟩, by wram_simp⟩
      wram_simp
      rcases eq_or_ne q (y.regs idx) with rfl | hne
      · exact le_of_not_gt hcmp
      · exact hM_ge q (by omega) hq'
  have hs₀ : ∃ s₀,
      ExecWithin w (ram[ rM ← #0; idx ← #0 ] : Code .standard 28) y₁ s₀ 2 ∧
      PM 0 s₀ ∧ s₀.regs idx = 0 := by
    refine WP.exists_execWithin ?_
    wram_exec
    exact ⟨⟨fun i hi hne => by wram_simp, hmem₁, by wram_simp; exact Nat.zero_le _,
      fun _ hq _ => by omega⟩, by wram_simp⟩
  obtain ⟨s₀, hes₀, hPs₀, hidxs₀⟩ := hs₀
  obtain ⟨y₂, hl₂, hPn₂, _⟩ := ExecWithin.loop_count PM
    (fun y hy => (hy.1 rnn (by decide) (by decide)).trans hb₁.hrnn) hbodyM
    (by omega) (hidxs₀ ▸ hPs₀)
  obtain ⟨hr₂, hm₂, hM_le₂, hM_ge₂⟩ := hPn₂
  have hb₂ : BaseRegs n bC (y₂.regs rM) y₂ :=
    ⟨(hr₂ zero (by decide) (by decide)).trans hb₁.hzero,
     (hr₂ one (by decide) (by decide)).trans hb₁.hone,
     (hr₂ two (by decide) (by decide)).trans hb₁.htwo,
     (hr₂ rn (by decide) (by decide)).trans hb₁.hrn,
     (hr₂ rnn (by decide) (by decide)).trans hb₁.hrnn,
     rfl,
     (hr₂ baseC (by decide) (by decide)).trans hb₁.hbaseC,
     (hr₂ baseY (by decide) (by decide)).trans hb₁.hbaseY,
     (hr₂ baseNZ (by decide) (by decide)).trans hb₁.hbaseNZ,
     (hr₂ baseColMate (by decide) (by decide)).trans hb₁.hbaseColMate,
     (hr₂ baseUsed (by decide) (by decide)).trans hb₁.hbaseUsed,
     (hr₂ baseTree (by decide) (by decide)).trans hb₁.hbaseTree,
     (hr₂ baseMinv (by decide) (by decide)).trans hb₁.hbaseMinv,
     (hr₂ baseBestRow (by decide) (by decide)).trans hb₁.hbaseBestRow,
     (hr₂ outBase (by decide) (by decide)).trans hb₁.houtBase,
     (hr₂ baseRowMate (by decide) (by decide)).trans hb₁.hbaseRowMate⟩
  refine ⟨y₂, (hes₀.seq hl₂).mono (by rw [hidxs₀, Nat.sub_zero]; nlinarith),
    hb₂, hm₂, hM_le₂, fun u v => ?_⟩
  have hq : u.val * n + v.val < n * n := Cslib.Matrix.pairIndex_lt (u, v)
  have h := hM_ge₂ (u.val * n + v.val) hq hq
  have hp_eq : (⟨u.val * n + v.val, hq⟩ : Fin (n * n)) = finProdFinEquiv (u, v) :=
    Fin.ext (Cslib.Matrix.pairIndex_eq_val_finProdFinEquiv (u, v))
  rwa [hp_eq, finProdFinEquiv.symm_apply_apply] at h

private theorem exec_fillCCode {w M : ℕ} (inst : Instance) (hw : Fits w inst.wordBound)
    (hM_le : M ≤ inst.maxMag) (hM_ge : ∀ u v : Fin inst.n, (inst.cost (u, v)).natAbs ≤ M)
    (y₂ : Data 28) (hb₂ : BaseRegs inst.n (2 + inst.n * inst.n) M y₂)
    (hmem₂ : y₂.mem = (Data.init inst.encode : Data 28).mem) :
    ∃ y₃, ExecWithin w fillCCode y₂ y₃ (12 * inst.n * inst.n + 3) ∧
      BaseRegs inst.n (2 + inst.n * inst.n) M y₃ ∧
      CostMem (2 + inst.n * inst.n) (fun p => (inst.cost p + (M : ℤ)).toNat) y₃.mem := by
  let n := inst.n
  let bC := 2 + n * n
  let x₀ : Data 28 := Data.init inst.encode
  let C : Fin n × Fin n → ℕ := fun p => (inst.cost p + (M : ℤ)).toNat
  let eC : ℕ → ℕ := fun q => if hq : q < n * n then C (finProdFinEquiv.symm ⟨q, hq⟩) else 0
  let PC (k : ℕ) (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 21 → y.regs i = y₂.regs i) ∧
      (∀ j < k, y.mem (bC + j) = eC j) ∧
      (∀ a, ¬(bC ≤ a ∧ a < bC + k) → y.mem a = x₀.mem a)
  have hbodyC (y : Data 28) (hy : PC (y.regs idx) y) (hlt : y.regs idx < n * n) :
      ∃ z, ExecWithin w fillCBody y z 10 ∧ PC (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hm, hf⟩ := hy
    have hby : BaseRegs n bC M y := hb₂.of_eq fun i hi => hr i (by omega)
    let p := finProdFinEquiv.symm ⟨y.regs idx, hlt⟩
    let u := p.1
    let v := p.2
    have hp_mul : u.val * n + v.val = y.regs idx :=
      (Cslib.Matrix.pairIndex_eq_val_finProdFinEquiv p).trans
        (congrArg Fin.val (finProdFinEquiv.apply_symm_apply ⟨y.regs idx, hlt⟩))
    have hload : y.mem (2 + y.regs idx) = Signed.encode (inst.cost (u, v)) := by
      rw [hf _ (by simp only [bC]; omega), ← hp_mul]
      exact inst.init_mem_cost u v
    have hdiv : Signed.encode (inst.cost (u, v)) / 2 = (inst.cost (u, v)).natAbs :=
      Signed.encode_div_two _
    have hmod : Signed.encode (inst.cost (u, v)) % 2 = if inst.cost (u, v) < 0 then 1 else 0 :=
      Signed.encode_mod_two _
    have hmag_M : (inst.cost (u, v)).natAbs ≤ M := hM_ge u v
    have hf1 : Fits w (2 + y.regs idx) :=
      hw.of_le (by unfold Instance.wordBound; simp only [n] at hlt; nlinarith)
    have hf2 : Fits w ((inst.cost (u, v)).natAbs) :=
      hw.of_le (by unfold Instance.wordBound; nlinarith)
    have hf3 : Fits w (bC + y.regs idx) :=
      hw.of_le (by unfold Instance.wordBound; simp only [bC, n] at hlt ⊢; nlinarith)
    have hf4 : Fits w (y.regs idx + 1) :=
      hw.of_le (by unfold Instance.wordBound; simp only [n] at hlt; nlinarith)
    have hstep : ∃ z, ExecWithin w fillCBody y z 10 ∧
        z.mem = Function.update y.mem (bC + y.regs idx) (eC (y.regs idx)) ∧
        (∀ i : Fin 28, i.val < 21 → z.regs i = y₂.regs i) ∧
        z.regs idx = y.regs idx + 1 := by
      refine WP.exists_execWithin ?_
      unfold fillCBody
      by_cases hneg : inst.cost (u, v) < 0
      · have hmod1 : (if inst.cost (u, v) < 0 then 1 else 0) = 1 := ite_eq_left hneg
        have heq_e : M - (inst.cost (u, v)).natAbs = eC (y.regs idx) := by
          simp only [eC, hlt, dite_true]
          change _ = C (u, v)
          simp only [C]
          omega
        have hsub_M : M - (inst.cost (u, v)).natAbs ≤ inst.maxMag :=
          (Nat.sub_le _ _).trans hM_le
        have hf_sub : Fits w (M - (inst.cost (u, v)).natAbs) :=
          hw.of_le (by unfold Instance.wordBound; nlinarith)
        wram_exec [hby.htwo, hby.hzero, hby.hone, hby.hrM, hby.hbaseC,
          hload, hdiv, hmod, hmod1, hmag_M, hf1, hf2, hf3, hf4, hf_sub]
        exact ⟨by wram_simp [heq_e], fun i hi => by wram_simp [hr i hi], by wram_simp⟩
      · have hmod0 : (if inst.cost (u, v) < 0 then 1 else 0) = 0 := ite_eq_right hneg
        have heq_e : M + (inst.cost (u, v)).natAbs = eC (y.regs idx) := by
          simp only [eC, hlt, dite_true]
          change _ = C (u, v)
          simp only [C]
          omega
        have hadd_M : M + (inst.cost (u, v)).natAbs ≤ 2 * inst.maxMag := by
          have := inst.natAbs_cost_le_maxMag u v
          omega
        have hf_add : Fits w (M + (inst.cost (u, v)).natAbs) :=
          hw.of_le (by unfold Instance.wordBound; nlinarith)
        wram_exec [hby.htwo, hby.hzero, hby.hone, hby.hrM, hby.hbaseC,
          hload, hdiv, hmod, hmod0, hf1, hf2, hf3, hf4, hf_add]
        exact ⟨by wram_simp [heq_e], fun i hi => by wram_simp [hr i hi], by wram_simp⟩
    obtain ⟨z, he, hmz, hrz, hiz⟩ := hstep
    obtain ⟨hm', hf'⟩ := prefix_write_step hm hf hmz
    exact ⟨z, he, ⟨hrz, hm', hf'⟩, hiz⟩
  obtain ⟨y₃, he₃, hr₃, hm₃, _⟩ := exec_forLoop PC
    (fun y hy => (hy.1 rnn (by decide)).trans hb₂.hrnn) hbodyC (x := y₂)
    ⟨fun i hi => by wram_simp, fun _ hj => by omega, fun a _ => congrFun hmem₂ a⟩
  refine ⟨y₃, he₃.mono (by nlinarith),
    hb₂.of_eq (fun i hi => hr₃ i (by omega)), fun u v => ?_⟩
  have hq : u.val * n + v.val < n * n := Cslib.Matrix.pairIndex_lt (u, v)
  have h := hm₃ (u.val * n + v.val) hq
  have hp_eq : (⟨u.val * n + v.val, hq⟩ : Fin (n * n)) = finProdFinEquiv (u, v) :=
    Fin.ext (Cslib.Matrix.pairIndex_eq_val_finProdFinEquiv (u, v))
  dsimp only [eC, n, bC, C] at h
  rw [dite_eq_left hq, hp_eq, finProdFinEquiv.symm_apply_apply] at h
  exact h

private theorem exec_sumCostCode {w M : ℕ} (inst : Instance) (hw : Fits w inst.wordBound)
    (hM_le : M ≤ inst.maxMag)
    (hC_cast : ∀ p : Fin inst.n × Fin inst.n,
      (((inst.cost p + (M : ℤ)).toNat : ℕ) : ℤ) = inst.cost p + (M : ℤ))
    (hC_le : ∀ u v : Fin inst.n, (inst.cost (u, v) + (M : ℤ)).toNat ≤ 2 * M)
    (y₄ : Data 28) (hb₄ : BaseRegs inst.n (2 + inst.n * inst.n) M y₄)
    (hC₄ : CostMem (2 + inst.n * inst.n) (fun p => (inst.cost p + (M : ℤ)).toNat) y₄.mem)
    (hrm_eq : ∀ u : Fin inst.n,
      y₄.mem ((2 + inst.n * inst.n) + inst.n * inst.n + 7 * inst.n + 1 + u.val) =
        (inst.assignedCol u).val) :
    ∃ y₆, ExecWithin w sumCostCode y₄ y₆ (10 * inst.n + 10) ∧
      BaseRegs inst.n (2 + inst.n * inst.n) M y₆ ∧
      y₆.mem = y₄.mem ∧
      y₆.regs acc = inst.encodedMinCost := by
  let n := inst.n
  let bC := 2 + n * n
  let C : Fin n × Fin n → ℕ := fun p => (inst.cost p + (M : ℤ)).toNat
  have hfit_core : Fits w (bC + n * n + 8 * n + 2 * (2 * M) + 2) :=
    hw.of_le (by unfold Instance.wordBound; simp only [bC, n]; nlinarith)
  let PS (k : ℕ) (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 21 → y.regs i = y₄.regs i) ∧
      y.mem = y₄.mem ∧
      y.regs acc = (((List.finRange n).take k).map fun u => C (u, inst.assignedCol u)).sum ∧
      y.regs acc ≤ k * (2 * M)
  have hbodyS (y : Data 28) (hy : PS (y.regs idx) y) (hlt : y.regs idx < n) :
      ∃ z, ExecWithin w sumCostBody y z 8 ∧ PS (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hmem, hacc_eq, hacc_le⟩ := hy
    let u : Fin n := ⟨y.regs idx, hlt⟩
    let v := inst.assignedCol u
    have hby : BaseRegs n bC M y := hb₄.of_eq fun i hi => hr i (by omega)
    have hrm_u : y.mem (bC + n * n + 7 * n + 1 + y.regs idx) = v.val := by
      rw [hmem]
      exact hrm_eq u
    have hmul : y.regs idx * n + v.val < n * n := Cslib.Matrix.pairIndex_lt (u, v)
    have hC_uv : y.mem (bC + (y.regs idx * n + v.val)) = C (u, v) := by
      rw [hmem]
      exact hC₄ u v
    have hC_uv_le : C (u, v) ≤ 2 * M := hC_le u v
    have hf1 : Fits w (bC + n * n + 7 * n + 1 + y.regs idx) := hfit_core.of_le (by omega)
    have hf2 : Fits w (y.regs idx * n) := hfit_core.of_le (by omega)
    have hf3 : Fits w (y.regs idx * n + v.val) := hfit_core.of_le (by omega)
    have hf4 : Fits w (bC + (y.regs idx * n + v.val)) := hfit_core.of_le (by omega)
    have hf5 : Fits w (y.regs acc + C (u, v)) :=
      hw.of_le (by
        have h1 : y.regs acc + C (u, v) ≤ (y.regs idx + 1) * (2 * M) := by nlinarith
        have h2 : (y.regs idx + 1) * (2 * M) ≤ n * (2 * inst.maxMag) :=
          Nat.mul_le_mul (by omega) (by omega)
        unfold Instance.wordBound
        simp only [n] at h2
        nlinarith)
    have hf6 : Fits w (y.regs idx + 1) := hfit_core.of_le (by omega)
    refine WP.exists_execWithin ?_
    unfold sumCostBody
    wram_exec [hby.hbaseRowMate, hby.hrn, hby.hbaseC, hby.hone,
      hrm_u, hC_uv, hf1, hf2, hf3, hf4, hf5, hf6]
    refine ⟨⟨fun i hi => by wram_simp [hr i hi], hmem, ?_, ?_⟩, by wram_simp⟩
    · wram_simp
      rw [List.take_succ_finRange hlt, List.map_append, List.sum_append, List.map_singleton,
        List.sum_singleton, ← hacc_eq]
    · wram_simp
      nlinarith
  have hs_init : ∃ s₀,
      ExecWithin w (ram[ acc ← #0; idx ← #0 ] : Code .standard 28) y₄ s₀ 2 ∧
      PS 0 s₀ ∧ s₀.regs idx = 0 := by
    refine WP.exists_execWithin ?_
    wram_exec
    exact ⟨⟨fun i hi => by wram_simp, rfl, by wram_simp; simp,
      by wram_simp; exact Nat.zero_le _⟩, by wram_simp⟩
  obtain ⟨s₀_sum, hes_sum, hPS₀, hidx_sum⟩ := hs_init
  obtain ⟨y₅, hl_sum, hPSn, _⟩ := ExecWithin.loop_count PS
    (fun y hy => (hy.1 rn (by decide)).trans hb₄.hrn) hbodyS (by omega) (hidx_sum ▸ hPS₀)
  obtain ⟨hr₅, hmem₅, hacc₅, hacc₅_le⟩ := hPSn
  have hb₅ : BaseRegs n bC M y₅ := hb₄.of_eq fun i hi => hr₅ i (by omega)
  have hsum_z : (y₅.regs acc : ℤ) =
      matchingCost inst.cost (hungarian inst.cost).matching + (n * M : ℕ) := by
    have htake : (List.finRange n).take n = List.finRange n :=
      List.take_of_length_le (by simp)
    have hfin_sum : ((List.finRange n).map fun u => C (u, inst.assignedCol u)).sum =
        ∑ u : Fin n, C (u, inst.assignedCol u) := by
      rw [← Fin.sum_univ_def]
    rw [htake, hfin_sum] at hacc₅
    rw [hacc₅, Nat.cast_sum]
    simp only [C, hC_cast]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      inst.sum_cost_assignedCol]
    push_cast
    ring
  set opt := matchingCost inst.cost (hungarian inst.cost).matching
  have hf_nM : Fits w (n * M) :=
    hw.of_le (by
      have : n * M ≤ n * inst.maxMag := Nat.mul_le_mul_left n hM_le
      unfold Instance.wordBound; simp only [n] at this; nlinarith)
  have hstep_enc : ∃ y₆,
      ExecWithin w
        (ram[ val ← rn * rM;
              if acc < val then [
                val2 ← val - acc; acc ← two * val2; acc ← acc + one
              ] else [
                val2 ← acc - val; acc ← two * val2 ] ] : Code .standard 28) y₅ y₆ 6 ∧
      (∀ i : Fin 28, i.val < 16 → y₆.regs i = y₅.regs i) ∧
      y₆.mem = y₄.mem ∧
      y₆.regs acc = Signed.encode opt := by
    refine WP.exists_execWithin ?_
    by_cases hlt_opt : y₅.regs acc < n * M
    · have hopt_neg : opt < 0 := by omega
      have hsub_le : y₅.regs acc ≤ n * M := le_of_lt hlt_opt
      have habs : opt.natAbs = n * M - y₅.regs acc := by omega
      have h_sub1 : n * M - y₅.regs acc ≤ n * inst.maxMag :=
        (Nat.sub_le _ _).trans (Nat.mul_le_mul_left n hM_le)
      have hf_d : Fits w (n * M - y₅.regs acc) :=
        hw.of_le (by unfold Instance.wordBound; simp only [n] at h_sub1; nlinarith)
      have hf_2d : Fits w (2 * (n * M - y₅.regs acc)) :=
        hw.of_le (by unfold Instance.wordBound; simp only [n] at h_sub1; nlinarith)
      have hf_2d1 : Fits w (2 * (n * M - y₅.regs acc) + 1) :=
        hw.of_le (by unfold Instance.wordBound; simp only [n] at h_sub1; nlinarith)
      wram_exec [hb₅.hrn, hb₅.hrM, hb₅.htwo, hb₅.hone, hlt_opt, hsub_le,
        hf_nM, hf_d, hf_2d, hf_2d1]
      refine ⟨fun i hi => by wram_simp, hmem₅, ?_⟩
      wram_simp
      unfold Signed.encode
      rw [habs, ite_eq_left hopt_neg]
    · have hopt_nonneg : ¬opt < 0 := by omega
      have hsub_le : n * M ≤ y₅.regs acc := le_of_not_gt hlt_opt
      have habs : opt.natAbs = y₅.regs acc - n * M := by omega
      have h_sub2 : y₅.regs acc - n * M ≤ n * (2 * inst.maxMag) :=
        (Nat.sub_le _ _).trans (hacc₅_le.trans (Nat.mul_le_mul_left n (by omega)))
      have hf_d : Fits w (y₅.regs acc - n * M) :=
        hw.of_le (by unfold Instance.wordBound; simp only [n] at h_sub2; nlinarith)
      have hf_2d : Fits w (2 * (y₅.regs acc - n * M)) :=
        hw.of_le (by unfold Instance.wordBound; simp only [n] at h_sub2; nlinarith)
      wram_exec [hb₅.hrn, hb₅.hrM, hb₅.htwo, hb₅.hone, hlt_opt, hsub_le,
        hf_nM, hf_d, hf_2d]
      refine ⟨fun i hi => by wram_simp, hmem₅, ?_⟩
      wram_simp
      unfold Signed.encode
      rw [habs, ite_eq_right hopt_nonneg, Nat.add_zero]
  obtain ⟨y₆, he_enc, hr₆, hmem₆, hacc₆⟩ := hstep_enc
  exact ⟨y₆, (hes_sum.seq (hl_sum.seq he_enc)).mono (by rw [hidx_sum]; omega),
    hb₅.of_eq hr₆, hmem₆, hacc₆⟩

private theorem exec_inputCode {w : ℕ} (inst : Instance) (hw : Fits w inst.wordBound) :
    ∃ y, ExecWithin w inputCode (Data.init inst.encode) y (hungarianTime inst.n - 1) ∧
      outputList y.mem (y.regs outBase) = inst.assignment ∧
      Fits w (y.regs outBase + inst.assignment.length) ∧
      y.regs acc = inst.encodedMinCost := by
  obtain ⟨y₁, he_setup, hb₁, hmem₁⟩ := exec_setupCode inst hw
  obtain ⟨y₂, he_scan, hb₂, hmem₂, hM_le, hM_ge⟩ := exec_scanMaxCode inst hw y₁ hb₁ hmem₁
  let M := y₂.regs rM
  let C : Fin inst.n × Fin inst.n → ℕ := fun p => (inst.cost p + (M : ℤ)).toNat
  have hC_cast : ∀ p : Fin inst.n × Fin inst.n, (C p : ℤ) = inst.cost p + (M : ℤ) := by
    rintro ⟨u, v⟩
    have := hM_ge u v
    simp only [C]
    omega
  have hC_le : ∀ u v : Fin inst.n, C (u, v) ≤ 2 * M := by
    intro u v
    have := hM_ge u v
    simp only [C]
    omega
  obtain ⟨y₃, he_fill, hb₃, hC₃⟩ := exec_fillCCode inst hw hM_le hM_ge y₂ hb₂ hmem₂
  have hfit_core :
      Fits w ((2 + inst.n * inst.n) + inst.n * inst.n + 8 * inst.n + 2 * (2 * M) + 2) :=
    hw.of_le (by unfold Instance.wordBound; nlinarith)
  obtain ⟨y₄, he_core, hr₄, _, _, hout_len, hrow_match, hf₄⟩ :=
    core_exec hC_le y₃ hb₃ hC₃ hfit_core
  have hb₄ : BaseRegs inst.n (2 + inst.n * inst.n) M y₄ := hb₃.of_eq hr₄
  have hC₄ : CostMem (2 + inst.n * inst.n) C y₄.mem := hC₃.of_outside fun a ha => hf₄ a (.inl ha)
  have hm_shift : (hungarian fun p => (C p : ℤ)).matching = (hungarian inst.cost).matching := by
    have hfun : (fun p => (C p : ℤ)) = (fun p => inst.cost p + (M : ℤ)) := funext hC_cast
    rw [hfun]
    exact (hungarian_add_const inst.cost (M : ℤ)).1
  have hrm_eq : ∀ u : Fin inst.n,
      y₄.mem ((2 + inst.n * inst.n) + inst.n * inst.n + 7 * inst.n + 1 + u.val) =
        (inst.assignedCol u).val := by
    intro u
    obtain ⟨v, hv_mem, hv_in⟩ := hrow_match u
    rw [hm_shift] at hv_in
    rw [hv_mem, inst.assignedCol_eq_of_mem hv_in]
  obtain ⟨y₆, he_sum, hb₆, hmem₆, hacc₆⟩ :=
    exec_sumCostCode inst hw hM_le hC_cast hC_le y₄ hb₄ hC₄ hrm_eq
  have hout_list : outputList y₆.mem (y₆.regs outBase) = inst.assignment := by
    rw [hb₆.houtBase, hmem₆]
    unfold outputList
    rw [hout_len]
    refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    have hi : i < inst.n := by simpa using h1
    simp only [List.getElem_map, List.getElem_range]
    rw [hrm_eq ⟨i, hi⟩, inst.getElem_assignment ⟨i, hi⟩]
  have hf_final : Fits w (y₆.regs outBase + inst.assignment.length) := by
    rw [hb₆.houtBase, inst.length_assignment]
    exact hw.of_le (by unfold Instance.wordBound; nlinarith)
  refine ⟨y₆, (he_setup.seq (he_scan.seq (he_fill.seq (he_core.seq he_sum)))).mono ?_,
    hout_list, hf_final, hacc₆⟩
  unfold hungarianTime coreTime
  rw [Nat.add_sub_assoc (by decide : 1 ≤ 52)]
  nlinarith

/-- **`O(n³)` Word-RAM minimum-cost perfect matching (`ExecutesList`).** On any `n × n` integer
assignment instance `inst` and word width `w` satisfying `Fits w inst.wordBound`,
`assignmentProgram` halts within `hungarianTime inst.n = 99 n³ + 91 n² + 58 n + 52` instructions
returning `inst.assignment` (`IsMinCostPerfectMatching`). -/
theorem executesList_assignment {w : ℕ} (inst : Instance) (hw : Fits w inst.wordBound) :
    ∃ steps, ExecutesList w assignmentProgram (.init inst.encode) inst.assignment steps ∧
      steps ≤ hungarianTime inst.n := by
  obtain ⟨y, ⟨t, ht, hex⟩, hout, hfit, _⟩ := exec_inputCode inst hw
  refine ⟨t + 1, hout ▸ hex.executesList outBase (by rwa [hout]), ?_⟩
  unfold hungarianTime at ht ⊢
  omega

/-- **`Program.ComputesListInTime` form of `executesList_assignment`.** -/
theorem computesListInTime_assignment :
    assignmentProgram.ComputesListInTime (fun _ inst => inst.encode)
      (fun inst _ => hungarianTime inst.n) (fun inst w => Fits w inst.wordBound)
      Instance.assignment :=
  fun inst _ hw _ => executesList_assignment inst hw

/-- **`O(n³)` Word-RAM minimum matching cost (`Executes`).** On any `n × n` integer assignment
instance `inst` and word width `w` satisfying `Fits w inst.wordBound`, `minCostProgram` halts
within `hungarianTime inst.n = 99 n³ + 91 n² + 58 n + 52` instructions returning
`Signed.encode (matchingCost inst.cost (hungarian inst.cost).matching)`. -/
theorem executes_minCost {w : ℕ} (inst : Instance) (hw : Fits w inst.wordBound) :
    ∃ steps, Executes w minCostProgram (.init inst.encode) inst.encodedMinCost steps ∧
      steps ≤ hungarianTime inst.n := by
  obtain ⟨y, ⟨t, ht, hex⟩, _, _, hacc⟩ := exec_inputCode inst hw
  refine ⟨t + 1, hacc ▸ hex.executes acc, ?_⟩
  unfold hungarianTime at ht ⊢
  omega

/-- **`Program.ComputesInTime` form of `executes_minCost`.** -/
theorem computesInTime_minCost :
    minCostProgram.ComputesInTime (fun _ inst => inst.encode)
      (fun inst _ => hungarianTime inst.n) (fun inst w => Fits w inst.wordBound)
      Instance.encodedMinCost :=
  fun inst _ hw _ => executes_minCost inst hw

end Cslib.Algorithms.WordRAM.Hungarian

