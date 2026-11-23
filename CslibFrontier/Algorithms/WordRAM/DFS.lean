/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.DFS.SCC
public import CslibFrontier.Computability.WordRAM.ListOutput
public import CslibFrontier.Computability.WordRAM.Notation
public import CslibFrontier.Computability.WordRAM.Allocation
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Ring

/-!
# Linear-time depth-first search on the word RAM

Iterative depth-first search with an explicit stack on the standard-basis word RAM
(`Cslib.WordRAM.Basis.standard`), after [Tarjan][Tarjan1972] and [Cormen et al., Sections
22.3–22.5][CLRS2009]: DFS finishing order, topological sort, CSR transposition and Kosaraju's
strongly connected components, each in `O(N + M)` instructions on a graph with `N` vertices and
`M` arcs, proved equal to the pure functions of `CslibFrontier.Algorithms.Lean.DFS`.

## Representation

A graph `adj : Fin N → List (Fin N)` is held in compressed sparse row form (`CSRAt`): an offset
array `csrOffset adj 0, …, csrOffset adj N` followed by the successor lists in order. All passes
work in one scratch layout based at an address `wb` (`kOffAddr`, …, `kTopAddr`), with `Mc` words
reserved for each arc array. The DFS stack holds `3` words per frame (vertex, next arc, arc end),
so no recursion is needed. The engine (`forwardDFSCode`, `transposeCSRCode`,
`kosarajuIndexCode`, `sccIndexCode` and their CSR primitives) is shared with
`CslibFrontier.Algorithms.WordRAM.TwoSAT`.

The end-to-end programs read a `Graph` in the CSR input encoding `Graph.encodeCSR`
(`[n, m, off 0, …, off n] ++ arcs`), so the input already is the forward CSR graph of the layout
based at `wb = 3`, and return a list through `Cslib.WordRAM.ExecutesList`.

## Main definitions

* `Cslib.Algorithms.WordRAM.DFS.csrOffset`, `Cslib.Algorithms.WordRAM.DFS.CSRAt`: CSR offsets and
  the CSR memory invariant.
* `Cslib.Algorithms.WordRAM.DFS.forwardDFSCode`, `Cslib.Algorithms.WordRAM.DFS.transposeCSRCode`,
  `Cslib.Algorithms.WordRAM.DFS.kosarajuIndexCode`, `Cslib.Algorithms.WordRAM.DFS.sccIndexCode`:
  the structured passes.
* `Cslib.Algorithms.WordRAM.DFS.Graph`, `Cslib.Algorithms.WordRAM.DFS.Graph.m`,
  `Cslib.Algorithms.WordRAM.DFS.Graph.encodeCSR`, `Cslib.Algorithms.WordRAM.DFS.Graph.wordBound`:
  graph instances, arc count, CSR input encoding and word-size envelope.
* `Cslib.Algorithms.WordRAM.DFS.topoWords`, `Cslib.Algorithms.WordRAM.DFS.sccWords`: outputs.
* `Cslib.Algorithms.WordRAM.DFS.topoProgram`, `Cslib.Algorithms.WordRAM.DFS.sccProgram`: flat
  programs.

## Main results

* `Cslib.Algorithms.WordRAM.DFS.forwardDFSCode_spec`: the forward pass writes the DFS finishing
  order `(topologicalSort adj (List.finRange N)).reverse` in `87 * N + 36 * Mc + 10` instructions.
* `Cslib.Algorithms.WordRAM.DFS.transposeCSRCode_spec`: CSR transposition (`transposeAdj`).
* `Cslib.Algorithms.WordRAM.DFS.kosarajuIndexCode_spec`: Kosaraju component peeling and indexing
  from a transposed CSR graph and finishing order.
* `Cslib.Algorithms.WordRAM.DFS.sccIndexCode_spec`: Kosaraju component indices
  `indexComponents (sccs adj (List.finRange N))` in `220 * N + 92 * Mc + 42` instructions.
* `Cslib.Algorithms.WordRAM.DFS.Graph.csrAt_init`,
  `Cslib.Algorithms.WordRAM.DFS.Graph.inputFits_encodeCSR`: the input encoding is a CSR graph
  whose words fit.
* `Cslib.Algorithms.WordRAM.DFS.topoCode_spec`,
  `Cslib.Algorithms.WordRAM.DFS.computesListInTime_topoProgram`: topological sort within
  `128 * (n + m + 1)` instructions at every width `w` with `Fits w G.wordBound`.
* `Cslib.Algorithms.WordRAM.DFS.sccCode_spec`,
  `Cslib.Algorithms.WordRAM.DFS.computesListInTime_sccProgram`: strongly connected component
  indices within `256 * (n + m + 1)` instructions.
* `Cslib.Algorithms.WordRAM.DFS.not_readsWidth_topoProgram`,
  `Cslib.Algorithms.WordRAM.DFS.not_readsWidth_sccProgram`: width independence.

## References

* [R. E. Tarjan, *Depth-first search and linear graph algorithms*][Tarjan1972]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.WordRAM.DFS

open Cslib.WordRAM
open Cslib.Algorithms.Lean.DFS

/-! ### Registers and scratch memory layout -/

namespace Reg
/-- Constant `0`. -/
abbrev cZero : Fin 28 := ⟨0, by decide⟩
/-- Constant `1`. -/
abbrev cOne : Fin 28 := ⟨1, by decide⟩
/-- Constant `3` (words per DFS stack frame). -/
abbrev cThree : Fin 28 := ⟨3, by decide⟩
/-- Vertex count `N`. -/
abbrev nVerts : Fin 28 := ⟨6, by decide⟩
/-- Base address of the CSR offset array being traversed. -/
abbrev offB : Fin 28 := ⟨8, by decide⟩
/-- Base address of the CSR edge array being traversed. -/
abbrev edgeB : Fin 28 := ⟨9, by decide⟩
/-- Base address of the visited-flag array. -/
abbrev visB : Fin 28 := ⟨10, by decide⟩
/-- Base address of the finishing-order output array. -/
abbrev finB : Fin 28 := ⟨11, by decide⟩
/-- Base address of the explicit DFS stack. -/
abbrev stkB : Fin 28 := ⟨12, by decide⟩
/-- Base address of the transpose fill cursors. -/
abbrev curB : Fin 28 := ⟨13, by decide⟩
/-- Base address of the transpose CSR offset array. -/
abbrev revOffB : Fin 28 := ⟨14, by decide⟩
/-- Base address of the transpose CSR edge array. -/
abbrev revEdgeB : Fin 28 := ⟨15, by decide⟩
/-- Base address of the forward finishing order. -/
abbrev ordB : Fin 28 := ⟨16, by decide⟩
/-- Base address of the component-index array. -/
abbrev compB : Fin 28 := ⟨17, by decide⟩
/-- Outer loop counter. -/
abbrev iReg : Fin 28 := ⟨18, by decide⟩
/-- Stack depth or inner loop counter. -/
abbrev pReg : Fin 28 := ⟨19, by decide⟩
/-- Number of finished vertices. -/
abbrev finCnt : Fin 28 := ⟨20, by decide⟩
/-- Current component index. -/
abbrev compIdxReg : Fin 28 := ⟨21, by decide⟩
/-- Finished count before the current root. -/
abbrev oldFinReg : Fin 28 := ⟨22, by decide⟩
/-- Current vertex. -/
abbrev uReg : Fin 28 := ⟨23, by decide⟩
/-- Current successor. -/
abbrev vReg : Fin 28 := ⟨24, by decide⟩
/-- Current edge position. -/
abbrev jReg : Fin 28 := ⟨25, by decide⟩
/-- End of the current edge range. -/
abbrev jEndReg : Fin 28 := ⟨26, by decide⟩
/-- Address scratch register. -/
abbrev addr : Fin 28 := ⟨27, by decide⟩
/-- Arc count `m` (end-to-end programs). -/
private abbrev mArcs : Fin 28 := ⟨2, by decide⟩
/-- Output-list header register (end-to-end programs). -/
abbrev outReg : Fin 28 := ⟨7, by decide⟩

end Reg

open Reg

local macro "reg_ne" : tactic =>
  `(tactic| exact Fin.ne_of_val_ne (by
    simp only [ne_eq, Fin.ext_iff, cZero, cOne, cThree, nVerts, offB, edgeB, visB, finB, stkB,
      curB, revOffB, revEdgeB, ordB, compB, iReg, pReg, finCnt, compIdxReg, oldFinReg, uReg, vReg,
      jReg, jEndReg, addr, mArcs, outReg] at *
    omega))

local macro "regs_lt" : tactic =>
  `(tactic| (
    repeat (first
      | rw [Data.write_regs_apply]
      | rw [Data.set_regs_of_ne (by reg_ne)])
    try rfl))

local macro "mem_upd" : tactic =>
  `(tactic| simp only [Data.set_mem, Data.set_mem_apply, Data.write_mem])

/-- Address of the forward CSR offset array in the scratch layout based at `wb`. -/
@[expose] def kOffAddr (wb : ℕ) : ℕ := wb
/-- Address of the forward CSR edge array. -/
@[expose] def kEdgeAddr (wb N : ℕ) : ℕ := wb + N + 1
/-- Address of the transpose CSR offset array. -/
@[expose] def kRevOffAddr (wb N Mc : ℕ) : ℕ := wb + N + 1 + Mc
/-- Address of the transpose CSR edge array. -/
@[expose] def kRevEdgeAddr (wb N Mc : ℕ) : ℕ := wb + 2 * N + 2 + Mc
/-- Address of the transpose fill cursors. -/
@[expose] def kCurAddr (wb N Mc : ℕ) : ℕ := wb + 2 * N + 2 + 2 * Mc
/-- Address of the visited-flag array. -/
@[expose] def kVisAddr (wb N Mc : ℕ) : ℕ := wb + 3 * N + 3 + 2 * Mc
/-- Address of the forward finishing order. -/
@[expose] def kOrdAddr (wb N Mc : ℕ) : ℕ := wb + 4 * N + 3 + 2 * Mc
/-- Address of the second-pass finishing order. -/
@[expose] def kFinAddr (wb N Mc : ℕ) : ℕ := wb + 5 * N + 3 + 2 * Mc
/-- Address of the explicit DFS stack (`3` words per frame). -/
@[expose] def kStkAddr (wb N Mc : ℕ) : ℕ := wb + 6 * N + 3 + 2 * Mc
/-- Address of the component-index array. -/
@[expose] def kCompAddr (wb N Mc : ℕ) : ℕ := wb + 9 * N + 3 + 2 * Mc
/-- First address past the scratch layout. -/
@[expose] def kTopAddr (wb N Mc : ℕ) : ℕ := wb + 10 * N + 3 + 2 * Mc

/-! ### Reusable CSR representation and shared array/CSR primitives -/

/-- Number of arcs leaving vertices below `u`: the CSR offset of vertex `u`. -/
@[expose] def csrOffset {N : ℕ} (adj : Fin N → List (Fin N)) (u : ℕ) : ℕ :=
  (((List.finRange N).take u).map fun w => (adj w).length).sum

@[simp]
theorem csrOffset_zero {N : ℕ} (adj : Fin N → List (Fin N)) :
    csrOffset adj 0 = 0 := rfl

theorem csrOffset_succ {N : ℕ} (adj : Fin N → List (Fin N)) {u : ℕ} (hu : u < N) :
    csrOffset adj (u + 1) = csrOffset adj u + (adj ⟨u, hu⟩).length := by
  unfold csrOffset
  have hlen : u < (List.finRange N).length := by simpa using hu
  rw [List.take_add_one, List.getElem?_eq_getElem hlen]
  simp

theorem csrOffset_mono {N : ℕ} (adj : Fin N → List (Fin N)) {a b : ℕ} (hab : a ≤ b) :
    csrOffset adj a ≤ csrOffset adj b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction d with
  | zero => simp
  | succ d ih =>
    by_cases hlt : a + d < N
    · rw [Nat.add_succ, csrOffset_succ adj hlt]
      exact ih.trans (Nat.le_add_right _ _)
    · have heq : csrOffset adj (a + (d + 1)) = csrOffset adj (a + d) := by
        unfold csrOffset
        rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)]
      rw [heq]
      exact ih

theorem csrOffset_eq_outDegreeSum {N : ℕ} (adj : Fin N → List (Fin N)) :
    csrOffset adj N = outDegreeSum adj (List.finRange N) := by
  unfold csrOffset outDegreeSum
  rw [List.take_of_length_le (by simp)]

/-- `adj` is stored in CSR form: offsets at `offBase`, successor lists at `edgeBase`. -/
@[expose] def CSRAt {N : ℕ} (adj : Fin N → List (Fin N)) (offBase edgeBase : ℕ)
    (mem : ℕ → ℕ) : Prop :=
  (∀ u ≤ N, mem (offBase + u) = csrOffset adj u) ∧
    ∀ (u : Fin N) (k : ℕ) (hk : k < (adj u).length),
      mem (edgeBase + csrOffset adj u.val + k) = ((adj u)[k]).val

private theorem CSRAt.of_eqOn {N : ℕ} {adj : Fin N → List (Fin N)} {offBase edgeBase : ℕ}
    {mem₁ mem₂ : ℕ → ℕ} (h : CSRAt adj offBase edgeBase mem₁)
    (hoff : ∀ u ≤ N, mem₂ (offBase + u) = mem₁ (offBase + u))
    (hedge : ∀ e < csrOffset adj N, mem₂ (edgeBase + e) = mem₁ (edgeBase + e)) :
    CSRAt adj offBase edgeBase mem₂ := by
  refine ⟨fun u hu => (hoff u hu).trans (h.1 u hu), fun u k hk => ?_⟩
  have hk_lt : csrOffset adj u.val + k < csrOffset adj N := by
    have h1 := csrOffset_succ adj u.isLt
    simp only [Fin.eta] at h1
    have h2 := csrOffset_mono adj (by omega : u.val + 1 ≤ N)
    omega
  rw [Nat.add_assoc, hedge _ hk_lt, ← Nat.add_assoc]
  exact h.2 u k hk

/-- Invariant of the backward CSR fill: the successor lists `part` written so far end at the cursors
`curBase`. -/
@[expose] def PartialCSRAt {N : ℕ} (targetAdj part : Fin N → List (Fin N))
    (curBase edgeBase : ℕ) (mem : ℕ → ℕ) : Prop :=
  (∀ w : Fin N, (part w).length ≤ (targetAdj w).length) ∧
    (∀ w : Fin N, mem (curBase + w.val) + (part w).length = csrOffset targetAdj (w.val + 1)) ∧
    ∀ (w : Fin N) (k : ℕ) (hk : k < (part w).length),
      mem (edgeBase + mem (curBase + w.val) + k) = ((part w)[k]).val

theorem partialCSRAt_init {N : ℕ} (targetAdj : Fin N → List (Fin N))
    (curBase edgeBase : ℕ) (mem : ℕ → ℕ)
    (hcur : ∀ w : Fin N, mem (curBase + w.val) = csrOffset targetAdj (w.val + 1)) :
    PartialCSRAt targetAdj (fun _ => []) curBase edgeBase mem :=
  ⟨fun _ => Nat.zero_le _, fun w => by simp [hcur w], fun _ _ hk => by simp at hk⟩

theorem csrAt_of_partialCSRAt {N : ℕ} (targetAdj : Fin N → List (Fin N))
    (offBase curBase edgeBase : ℕ) (mem : ℕ → ℕ)
    (hoff : ∀ u ≤ N, mem (offBase + u) = csrOffset targetAdj u)
    (hp : PartialCSRAt targetAdj targetAdj curBase edgeBase mem) :
    CSRAt targetAdj offBase edgeBase mem := by
  refine ⟨hoff, fun u k hk => ?_⟩
  have hcur_u := hp.2.1 u
  rw [csrOffset_succ targetAdj u.isLt] at hcur_u
  simp only [Fin.eta] at hcur_u
  have heq : mem (curBase + u.val) = csrOffset targetAdj u.val := by omega
  have hget := hp.2.2 u k hk
  rwa [heq] at hget

/-- Zero `[baseReg, baseReg + nVerts)` in `4 * N + 4` instructions via `Cslib.WordRAM.zeroFill`. -/
def zeroBlockCode (baseReg : Fin 28) : Code .standard 28 :=
  (ram[ addr ← baseReg; jEndReg ← baseReg + nVerts ]).seq
    (zeroFill addr jEndReg cZero cOne)

theorem zeroBlockCode_spec {w : ℕ} (baseReg : Fin 28) (hbr : baseReg.val < 18)
    (B N : ℕ) (hfit : Fits w (B + N)) {x : Data 28}
    (hc0 : x.regs cZero = 0) (hc1 : x.regs cOne = 1)
    (hB : x.regs baseReg = B) (hN : x.regs nVerts = N) :
    ∃ y, ExecWithin w (zeroBlockCode baseReg) x y (4 * N + 4) ∧
      (∀ i < N, y.mem (B + i) = 0) ∧
      (∀ a, ¬ (B ≤ a ∧ a < B + N) → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r) := by
  let x₁ := (x.set addr B).set jEndReg (B + N)
  have hprep : ExecWithin (B := .standard) w
      (ram[ addr ← baseReg; jEndReg ← baseReg + nVerts ]) x x₁ 2 := by
    have hb_ne : baseReg ≠ addr := by reg_ne
    have hn_ne : nVerts ≠ addr := by reg_ne
    have heval : BinOp.add.eval ((x.set addr B).regs baseReg) ((x.set addr B).regs nVerts) =
        B + N := by
      rw [Data.set_regs_of_ne hb_ne, Data.set_regs_of_ne hn_ne, hB, hN]; rfl
    have he1 : Exec (B := .standard) w (ram[ addr ← baseReg ]) x (x.set addr B) 1 := by
      simpa [hB] using (Exec.copy (B := .standard) (w := w) (x := x) (d := addr) (s := baseReg))
    have he2 : Exec (B := .standard) w (ram[ jEndReg ← baseReg + nVerts ]) (x.set addr B) x₁ 1 := by
      have hfit' : Fits w (BinOp.add.eval ((x.set addr B).regs baseReg)
          ((x.set addr B).regs nVerts)) := by rwa [heval]
      have h : Exec (B := .standard) w (ram[ jEndReg ← baseReg + nVerts ]) (x.set addr B) _ 1 :=
        Exec.bin hfit'
      rwa [heval] at h
    exact ⟨2, le_rfl, he1.seq he2⟩
  have hx₁_addr : x₁.regs addr = B := by dsimp only [x₁]; wram_simp
  have hx₁_stop : x₁.regs jEndReg = B + N := by dsimp only [x₁]; wram_simp
  have hx₁_0 : x₁.regs cZero = 0 := by dsimp only [x₁]; wram_simp; exact hc0
  have hx₁_1 : x₁.regs cOne = 1 := by dsimp only [x₁]; wram_simp; exact hc1
  have hzf := zeroFill_exec (w := w) (cur := addr) (stop := jEndReg) (zero := cZero) (one := cOne)
    (x := x₁) (by decide) (by decide) (by decide) hx₁_0 hx₁_1
    (by rw [hx₁_addr, hx₁_stop]; omega) (by rw [hx₁_stop]; exact hfit)
  rw [hx₁_addr, hx₁_stop, Nat.add_sub_cancel_left] at hzf
  have hzf_w : ExecWithin w (zeroFill addr jEndReg cZero cOne) x₁
      ⟨Function.update x₁.regs addr (B + N), clear x₁.mem B N⟩ (4 * N + 2) :=
    ⟨4 * N + 2, le_rfl, hzf⟩
  refine ⟨_, (hprep.seq hzf_w).mono (by omega), fun i hi => ?_, fun a ha => ?_, fun r hr => ?_⟩
  · exact clear_of_owns ⟨Nat.le_add_right B i, Nat.add_lt_add_left hi B⟩
  · exact clear_of_not_owns ha
  · have hne1 : r ≠ addr := by reg_ne
    simp only [x₁, Function.update_of_ne hne1]
    regs_lt

/-- `zeroBlockCode baseReg` does not read the word width. -/
theorem not_readsWidth_zeroBlockCode (baseReg : Fin 28) :
    ¬ (zeroBlockCode baseReg).ReadsWidth := by
  revert baseReg; decide +kernel

/-- `zeroBlockCode baseReg` is `rand`-free. -/
theorem isRandFree_zeroBlockCode (baseReg : Fin 28) :
    (zeroBlockCode baseReg).IsRandFree := by
  revert baseReg; decide +kernel

/-- Increment `mem[curB + vReg]` by `1` in `4` instructions. -/
def incCurCode : Code .standard 28 := ram[
  addr ← curB + vReg; jEndReg ← *addr; jEndReg ← jEndReg + cOne; *addr ← jEndReg ]

/-- `incCurCode` does not read the word width. -/
theorem not_readsWidth_incCurCode : ¬ incCurCode.ReadsWidth := by decide +kernel

/-- `incCurCode` is `rand`-free. -/
theorem isRandFree_incCurCode : incCurCode.IsRandFree := by decide +kernel

theorem incCurCode_spec {N w : ℕ} (curBase maxDeg : ℕ)
    (hfit : Fits w (curBase + N + maxDeg + 1))
    (deg : Fin N → ℕ) (src : Fin N) (hdeg_le : deg src + 1 ≤ maxDeg)
    {x : Data 28} (hc1 : x.regs cOne = 1) (hcur : x.regs curB = curBase)
    (hsrc : x.regs vReg = src.val)
    (hmem : ∀ u : Fin N, x.mem (curBase + u.val) = deg u) :
    ∃ y, ExecWithin w incCurCode x y 4 ∧
      (∀ u : Fin N, y.mem (curBase + u.val) = Function.update deg src (deg src + 1) u) ∧
      (∀ a, ¬ (curBase ≤ a ∧ a < curBase + N) → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r ≠ addr → r ≠ jEndReg → y.regs r = x.regs r) := by
  have hlt := src.isLt
  have hm_src := hmem src
  have hf_addr : Fits w (curBase + src.val) := hfit.of_le (by omega)
  have hf_val : Fits w (deg src + 1) := hfit.of_le (by omega)
  let IncPost (y : Data 28) : Prop :=
    (∀ u : Fin N, y.mem (curBase + u.val) = Function.update deg src (deg src + 1) u) ∧
      (∀ a, ¬ (curBase ≤ a ∧ a < curBase + N) → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r ≠ addr → r ≠ jEndReg → y.regs r = x.regs r)
  change ∃ y, ExecWithin w incCurCode x y 4 ∧ IncPost y
  unfold incCurCode
  wram_exec [hc1, hcur, hsrc, hm_src, hf_addr, hf_val]
  dsimp only [IncPost]
  refine ⟨fun u => ?_, fun a ha => ?_, fun r h1 h2 => ?_⟩
  · mem_upd
    by_cases hu : u = src
    · subst hu; simp
    · have hne : curBase + u.val ≠ curBase + src.val := fun h => hu (Fin.ext (by omega))
      simp [Function.update_of_ne hne, Function.update_of_ne hu, hmem u]
  · mem_upd
    exact Function.update_of_ne (by omega) _ _
  · regs_lt

/-- Compute CSR prefix sums `offB[0..N]` from degrees in `curB[0..N)` and set
`curB[u] := offB[u + 1]` in `9 * N + 5` instructions. -/
private def prefixSumBody : Code .standard 28 := ram[
  addr ← curB + iReg; uReg ← *addr;
  pReg ← pReg + uReg;
  *addr ← pReg;
  iReg ← iReg + cOne;
  addr ← offB + iReg; *addr ← pReg ]

/-- Prefix sums turning out-degrees at `offB` into CSR offsets and fill cursors. -/
def prefixSumCode : Code .standard 28 :=
  (ram[ *offB ← cZero; pReg ← cZero; iReg ← cZero ]).seq
    (.loop (.lt iReg nVerts) prefixSumBody)

/-- `prefixSumCode` does not read the word width. -/
theorem not_readsWidth_prefixSumCode : ¬ prefixSumCode.ReadsWidth := by decide +kernel

/-- `prefixSumCode` is `rand`-free. -/
theorem isRandFree_prefixSumCode : prefixSumCode.IsRandFree := by decide +kernel

theorem prefixSumCode_spec {N w : ℕ} (targetAdj : Fin N → List (Fin N))
    (degBase offBase Mc : ℕ) (hdisj : offBase + N + 1 ≤ degBase)
    (hmc : csrOffset targetAdj N ≤ Mc)
    (hfit : Fits w (degBase + N + Mc + 2))
    {x : Data 28} (hc0 : x.regs cZero = 0) (hc1 : x.regs cOne = 1)
    (hdegB : x.regs curB = degBase) (hoffB : x.regs offB = offBase)
    (hL : x.regs nVerts = N)
    (hdeg : ∀ u : Fin N, x.mem (degBase + u.val) = (targetAdj u).length) :
    ∃ y, ExecWithin w prefixSumCode x y (9 * N + 5) ∧
      (∀ u ≤ N, y.mem (offBase + u) = csrOffset targetAdj u) ∧
      (∀ u : Fin N, y.mem (degBase + u.val) = csrOffset targetAdj (u.val + 1)) ∧
      (∀ a, ¬ ((offBase ≤ a ∧ a < offBase + N + 1) ∨ (degBase ≤ a ∧ a < degBase + N)) →
        y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r) := by
  have hprep : ∃ x₀, ExecWithin (B := .standard) w
      (ram[ *offB ← cZero; pReg ← cZero; iReg ← cZero ]) x x₀ 3 ∧
      x₀.mem = Function.update x.mem offBase 0 ∧
      x₀.regs pReg = 0 ∧ x₀.regs iReg = 0 ∧
      (∀ r : Fin 28, r.val < 18 → x₀.regs r = x.regs r) := by
    let PrepPost (x₀ : Data 28) : Prop :=
      x₀.mem = Function.update x.mem offBase 0 ∧
        x₀.regs pReg = 0 ∧ x₀.regs iReg = 0 ∧
        (∀ r : Fin 28, r.val < 18 → x₀.regs r = x.regs r)
    change ∃ x₀, ExecWithin (B := .standard) w
      (ram[ *offB ← cZero; pReg ← cZero; iReg ← cZero ]) x x₀ 3 ∧ PrepPost x₀
    wram_exec [hc0, hoffB]
    dsimp only [PrepPost]
    refine ⟨by wram_simp, by wram_simp, by wram_simp, fun r hr => ?_⟩
    regs_lt
  obtain ⟨x₀, hx₀_ex, hx₀_mem, hx₀_p, hx₀_i, hx₀_fr⟩ := hprep
  let P (k : ℕ) (y : Data 28) : Prop :=
    (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r) ∧
      y.regs pReg = csrOffset targetAdj k ∧
      (∀ u ≤ k, y.mem (offBase + u) = csrOffset targetAdj u) ∧
      (∀ u : Fin N, y.mem (degBase + u.val) =
        if u.val < k then csrOffset targetAdj (u.val + 1) else (targetAdj u).length) ∧
      (∀ a, ¬ ((offBase ≤ a ∧ a ≤ offBase + k) ∨ (degBase ≤ a ∧ a < degBase + k)) →
        y.mem a = x.mem a)
  have hbody : ∀ y, P (y.regs iReg) y → y.regs iReg < N →
      ∃ z, ExecWithin w prefixSumBody y z 7 ∧
        P (y.regs iReg + 1) z ∧ z.regs iReg = y.regs iReg + 1 := by
    intro y ⟨hy_fr, hy_p, hy_off, hy_deg, hy_out⟩ hlt
    have hy1 : y.regs cOne = 1 := (hy_fr cOne (by decide)).trans hc1
    have hyD : y.regs curB = degBase := (hy_fr curB (by decide)).trans hdegB
    have hyO : y.regs offB = offBase := (hy_fr offB (by decide)).trans hoffB
    have hdeg_k : y.mem (degBase + y.regs iReg) = (targetAdj ⟨y.regs iReg, hlt⟩).length := by
      have := hy_deg ⟨y.regs iReg, hlt⟩
      simpa using this
    have hoff_succ : csrOffset targetAdj (y.regs iReg + 1) =
        csrOffset targetAdj (y.regs iReg) + (targetAdj ⟨y.regs iReg, hlt⟩).length :=
      csrOffset_succ targetAdj hlt
    have hoff_le : csrOffset targetAdj (y.regs iReg + 1) ≤ Mc :=
      (csrOffset_mono targetAdj (by omega : y.regs iReg + 1 ≤ N)).trans hmc
    have hf_daddr : Fits w (degBase + y.regs iReg) := hfit.of_le (by omega)
    have hf_psum : Fits w (csrOffset targetAdj (y.regs iReg) +
        (targetAdj ⟨y.regs iReg, hlt⟩).length) :=
      hfit.of_le (by omega)
    have hf_k1 : Fits w (y.regs iReg + 1) := hfit.of_le (by omega)
    have hf_oaddr : Fits w (offBase + (y.regs iReg + 1)) := hfit.of_le (by omega)
    let BodyPost (z : Data 28) : Prop :=
      P (y.regs iReg + 1) z ∧ z.regs iReg = y.regs iReg + 1
    change ∃ z, ExecWithin w prefixSumBody y z 7 ∧ BodyPost z
    unfold prefixSumBody
    wram_exec [hy1, hyD, hyO, hy_p, hdeg_k, hf_daddr, hf_psum, hf_k1, hf_oaddr]
    dsimp only [BodyPost, P]
    refine ⟨⟨fun r hr => ?_, ?_, fun u hu => ?_, fun u => ?_, fun a ha => ?_⟩, by wram_simp⟩
    · regs_lt; exact hy_fr r hr
    · wram_simp; exact hoff_succ.symm
    · mem_upd
      by_cases huk : u = y.regs iReg + 1
      · subst huk; simp [hoff_succ]
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hy_off u (by omega)
    · mem_upd
      rw [Function.update_of_ne (by have := u.isLt; omega)]
      by_cases huk : u.val = y.regs iReg
      · rw [huk, Function.update_self]
        simp [hoff_succ]
      · rw [Function.update_of_ne (by omega), hy_deg u]
        by_cases hlt' : u.val < y.regs iReg
        · have hlt'' : u.val < y.regs iReg + 1 := by omega
          simp [hlt', hlt'']
        · have hlt'' : ¬ u.val < y.regs iReg + 1 := by omega
          simp [hlt', hlt'']
    · mem_upd
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hy_out a (by omega)
  have hx₀_P : P (x₀.regs iReg) x₀ := by
    rw [hx₀_i]
    refine ⟨hx₀_fr, hx₀_p, fun u hu => ?_, fun u => ?_, fun a ha => ?_⟩
    · have hu0 : u = 0 := by omega
      subst hu0; simp [hx₀_mem]
    · simp only [Nat.not_lt_zero, ↓reduceIte, hx₀_mem]
      rw [Function.update_of_ne (by omega)]
      exact hdeg u
    · rw [hx₀_mem, Function.update_of_ne (by omega)]
  obtain ⟨y, hy_loop, hy_P, -⟩ := ExecWithin.loop_count P
    (fun y hy => (hy.1 nVerts (by decide)).trans hL) hbody
    (x := x₀) (by omega) hx₀_P
  refine ⟨y, (hx₀_ex.seq hy_loop).mono (by omega), hy_P.2.2.1, fun u => ?_, fun a ha => ?_,
    hy_P.1⟩
  · simpa [u.isLt] using hy_P.2.2.2.1 u
  · exact hy_P.2.2.2.2 a (by omega)

/-- Decrement `curB[vReg]` and write `uReg` into `edgeB[curB[vReg]]` in `6` instructions. -/
def backfillStepCode : Code .standard 28 := ram[
  addr ← curB + vReg;
  jEndReg ← *addr; jEndReg ← jEndReg - cOne;
  *addr ← jEndReg;
  addr ← edgeB + jEndReg; *addr ← uReg ]

/-- `backfillStepCode` does not read the word width. -/
theorem not_readsWidth_backfillStepCode : ¬ backfillStepCode.ReadsWidth := by decide +kernel

/-- `backfillStepCode` is `rand`-free. -/
theorem isRandFree_backfillStepCode : backfillStepCode.IsRandFree := by decide +kernel

private theorem csrOffset_disjoint {N : ℕ} (adj : Fin N → List (Fin N)) {u v : Fin N}
    (hne : u ≠ v) {p q : ℕ}
    (hp1 : csrOffset adj u.val ≤ p) (hp2 : p < csrOffset adj (u.val + 1))
    (hq1 : csrOffset adj v.val ≤ q) (hq2 : q < csrOffset adj (v.val + 1)) : p ≠ q := by
  have hval : u.val ≠ v.val := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hval with hlt | hgt
  · have := csrOffset_mono adj (by omega : u.val + 1 ≤ v.val)
    omega
  · have := csrOffset_mono adj (by omega : v.val + 1 ≤ u.val)
    omega

private theorem partialCSRAt_step {N : ℕ}
    (targetAdj part : Fin N → List (Fin N))
    (curBase edgeBase Mc : ℕ)
    (hdisj : edgeBase + Mc ≤ curBase)
    (hmc : csrOffset targetAdj N ≤ Mc)
    (src dst : Fin N) (hroom : (part src).length + 1 ≤ (targetAdj src).length)
    (mem : ℕ → ℕ)
    (hp : PartialCSRAt targetAdj part curBase edgeBase mem) :
    let c := mem (curBase + src.val) - 1
    let mem' := Function.update (Function.update mem (curBase + src.val) c) (edgeBase + c) dst.val
    PartialCSRAt targetAdj (Function.update part src (dst :: part src)) curBase edgeBase mem' ∧
      (∀ a, ¬ ((curBase ≤ a ∧ a < curBase + N) ∨
          (edgeBase ≤ a ∧ a < edgeBase + csrOffset targetAdj N)) → mem' a = mem a) := by
  dsimp only
  have hsrc_lt := src.isLt
  have hcur_eq := hp.2.1 src
  have hoff_src : csrOffset targetAdj (src.val + 1) =
      csrOffset targetAdj src.val + (targetAdj src).length := by
    simpa using csrOffset_succ targetAdj hsrc_lt
  have hoff_le_N := csrOffset_mono targetAdj (by omega : src.val + 1 ≤ N)
  set c := mem (curBase + src.val) - 1
  set mem₁ := Function.update mem (curBase + src.val) c
  set mem' := Function.update mem₁ (edgeBase + c) dst.val
  have hc_pos : 1 ≤ mem (curBase + src.val) := by omega
  have hc_low : csrOffset targetAdj src.val ≤ c := by omega
  have hc_high : c < csrOffset targetAdj (src.val + 1) := by omega
  have hc_lt_N : c < csrOffset targetAdj N := lt_of_lt_of_le hc_high hoff_le_N
  refine ⟨⟨fun u => ?_, fun u => ?_, fun u k hk => ?_⟩, fun a ha => ?_⟩
  · by_cases hu : u = src
    · subst hu; simp [hroom]
    · simp [Function.update_of_ne hu, hp.1 u]
  · have hm_ne : edgeBase + c ≠ curBase + u.val := by have := u.isLt; omega
    rw [show mem' (curBase + u.val) = mem₁ (curBase + u.val) from
      Function.update_of_ne hm_ne.symm _ _]
    rcases eq_or_ne src u with rfl | hu
    · rw [Function.update_self, show mem₁ (curBase + src.val) = c from Function.update_self _ _ _,
        List.length_cons]
      omega
    · have hne : curBase + u.val ≠ curBase + src.val := fun h => hu (Fin.ext (by omega)).symm
      rw [Function.update_of_ne hu.symm,
        show mem₁ (curBase + u.val) = mem (curBase + u.val) from Function.update_of_ne hne _ _]
      exact hp.2.1 u
  · rcases eq_or_ne src u with rfl | hu
    · have hlen_upd : (Function.update part src (dst :: part src) src).length =
          (part src).length + 1 := by simp
      have hm_cur : mem' (curBase + src.val) = c := by
        change Function.update mem₁ (edgeBase + c) dst.val (curBase + src.val) = c
        rw [Function.update_of_ne (by omega)]
        exact Function.update_self _ _ _
      rw [hm_cur]
      have hget_upd : ∀ j (hj : j < (Function.update part src (dst :: part src) src).length),
          (Function.update part src (dst :: part src) src)[j] =
            (dst :: part src)[j]'(by simpa [hlen_upd] using hj) := by
        intro j hj
        simp
      rw [hget_upd k hk]
      cases k with
      | zero =>
        change Function.update mem₁ (edgeBase + c) dst.val (edgeBase + c + 0) = dst.val
        rw [Nat.add_zero, Function.update_self]
      | succ k' =>
        have hk' : k' < (part src).length := by omega
        have hidx : edgeBase + c + (k' + 1) = edgeBase + mem (curBase + src.val) + k' := by omega
        change Function.update mem₁ (edgeBase + c) dst.val (edgeBase + c + (k' + 1)) =
          ((part src)[k']).val
        rw [hidx, Function.update_of_ne (by omega)]
        change Function.update mem (curBase + src.val) c (edgeBase + mem (curBase + src.val) + k') =
          ((part src)[k']).val
        rw [Function.update_of_ne (by omega)]
        exact hp.2.2 src k' hk'
    · have hu' : u ≠ src := hu.symm
      have hget_upd : ∀ j (hj : j < (Function.update part src (dst :: part src) u).length),
          (Function.update part src (dst :: part src) u)[j] =
            (part u)[j]'(by simpa [Function.update_of_ne hu'] using hj) := by
        intro j hj
        simp [Function.update_of_ne hu']
      rw [hget_upd k hk]
      have hk_u : k < (part u).length := by simpa [Function.update_of_ne hu'] using hk
      have hne_c : curBase + u.val ≠ curBase + src.val := fun h => hu' (Fin.ext (by omega))
      have hm_cur : mem' (curBase + u.val) = mem (curBase + u.val) := by
        change Function.update mem₁ (edgeBase + c) dst.val (curBase + u.val) = mem (curBase + u.val)
        rw [Function.update_of_ne (by have := u.isLt; omega)]
        exact Function.update_of_ne hne_c _ _
      rw [hm_cur]
      have hu_cur := hp.2.1 u
      have hu_len := hp.1 u
      have hu_off : csrOffset targetAdj (u.val + 1) =
          csrOffset targetAdj u.val + (targetAdj u).length := by
        simpa using csrOffset_succ targetAdj u.isLt
      have hq_low : csrOffset targetAdj u.val ≤ mem (curBase + u.val) + k := by omega
      have hq_high : mem (curBase + u.val) + k < csrOffset targetAdj (u.val + 1) := by omega
      have hne_edge : mem (curBase + u.val) + k ≠ c :=
        csrOffset_disjoint targetAdj hu' hq_low hq_high hc_low hc_high
      have hq_lt_N : mem (curBase + u.val) + k < csrOffset targetAdj N :=
        lt_of_lt_of_le hq_high (csrOffset_mono targetAdj (by omega : u.val + 1 ≤ N))
      change Function.update mem₁ (edgeBase + c) dst.val (edgeBase + mem (curBase + u.val) + k) = _
      rw [Function.update_of_ne (by omega)]
      change Function.update mem (curBase + src.val) c (edgeBase + mem (curBase + u.val) + k) = _
      rw [Function.update_of_ne (by omega)]
      exact hp.2.2 u k hk_u
  · change Function.update (Function.update mem (curBase + src.val) c) (edgeBase + c) dst.val a =
      mem a
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

theorem backfillStepCode_spec {N w : ℕ}
    (targetAdj part : Fin N → List (Fin N))
    (curBase edgeBase Mc : ℕ)
    (hdisj : edgeBase + Mc ≤ curBase)
    (hmc : csrOffset targetAdj N ≤ Mc)
    (hfit : Fits w (curBase + N + Mc + 1))
    (src dst : Fin N) (hroom : (part src).length + 1 ≤ (targetAdj src).length)
    {x : Data 28} (hc1 : x.regs cOne = 1)
    (hcurB : x.regs curB = curBase) (hedgeB : x.regs edgeB = edgeBase)
    (hsrc : x.regs vReg = src.val) (hdst : x.regs uReg = dst.val)
    (hp : PartialCSRAt targetAdj part curBase edgeBase x.mem) :
    ∃ y, ExecWithin w backfillStepCode x y 6 ∧
      PartialCSRAt targetAdj (Function.update part src (dst :: part src)) curBase edgeBase y.mem ∧
      (∀ a, ¬ ((curBase ≤ a ∧ a < curBase + N) ∨
          (edgeBase ≤ a ∧ a < edgeBase + csrOffset targetAdj N)) → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r ≠ addr → r ≠ jEndReg → y.regs r = x.regs r) := by
  have hsrc_lt := src.isLt
  have hcur_eq := hp.2.1 src
  have hoff_src : csrOffset targetAdj (src.val + 1) =
      csrOffset targetAdj src.val + (targetAdj src).length := by
    simpa using csrOffset_succ targetAdj hsrc_lt
  have hoff_le_N := csrOffset_mono targetAdj (by omega : src.val + 1 ≤ N)
  set c := x.mem (curBase + src.val) - 1
  have hc_pos : 1 ≤ x.mem (curBase + src.val) := by omega
  have hc_lt_N : c < csrOffset targetAdj N :=
    lt_of_lt_of_le (by omega : c < csrOffset targetAdj (src.val + 1)) hoff_le_N
  have hf_caddr : Fits w (curBase + src.val) := hfit.of_le (by omega)
  have hf_eaddr : Fits w (edgeBase + c) := hfit.of_le (by omega)
  have hstep := partialCSRAt_step targetAdj part curBase edgeBase Mc hdisj hmc src dst hroom
    x.mem hp
  let BfPost (y : Data 28) : Prop :=
    PartialCSRAt targetAdj (Function.update part src (dst :: part src)) curBase edgeBase y.mem ∧
      (∀ a, ¬ ((curBase ≤ a ∧ a < curBase + N) ∨
          (edgeBase ≤ a ∧ a < edgeBase + csrOffset targetAdj N)) → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r ≠ addr → r ≠ jEndReg → y.regs r = x.regs r)
  change ∃ y, ExecWithin w backfillStepCode x y 6 ∧ BfPost y
  unfold backfillStepCode
  wram_exec [hc1, hcurB, hedgeB, hsrc, hdst, hf_caddr, hf_eaddr]
  dsimp only [BfPost]
  refine ⟨?_, fun a ha => ?_, fun r h1 h2 => ?_⟩
  · mem_upd; exact hstep.1
  · mem_upd; exact hstep.2 a ha
  · regs_lt

/-! ### Explicit-stack iterative CSR depth-first search (`O(N + M)`) -/

/-- Pure depth-first search over the successor list `es` from the visited set `vis` with an empty
finishing list. -/
private def foldEmpty {V : Type*} [DecidableEq V] (adj : V → List V) (k : ℕ)
    (es : List V) (vis : Finset V) : Cslib.Algorithms.Lean.DFS.State V :=
  es.foldl (fun t v => visit adj k v t) ⟨vis, []⟩

private theorem foldl_visit_append {V : Type*} [DecidableEq V] (adj : V → List V) (k : ℕ) :
    ∀ (es : List V) (vis : Finset V) (fin : List V),
      es.foldl (fun t v => visit adj k v t) ⟨vis, fin⟩ =
        ⟨(foldEmpty adj k es vis).visited, (foldEmpty adj k es vis).finished ++ fin⟩
  | [], _, _ => rfl
  | v :: es, vis, fin => by
    dsimp only [foldEmpty, List.foldl_cons]
    rw [visit_eq_of_nil k v vis fin, foldl_visit_append adj k es _ _,
      foldl_visit_append adj k es _ _, List.append_assoc]

private theorem foldEmpty_cons {V : Type*} [DecidableEq V] (adj : V → List V) (k : ℕ)
    (v : V) (es : List V) (vis : Finset V) :
    foldEmpty adj k (v :: es) vis =
      let s₁ := visit adj k v ⟨vis, []⟩
      let s₂ := foldEmpty adj k es s₁.visited
      ⟨s₂.visited, s₂.finished ++ s₁.finished⟩ := by
  dsimp only [foldEmpty, List.foldl_cons]
  exact foldl_visit_append adj k es (visit adj k v ⟨vis, []⟩).visited
    (visit adj k v ⟨vis, []⟩).finished

private theorem visit_eq_foldEmpty {V : Type*} [DecidableEq V] {adj : V → List V} {k : ℕ}
    {u : V} {vis : Finset V} (hu : u ∉ vis) :
    visit adj (k + 1) u ⟨vis, []⟩ =
      let s := foldEmpty adj k (adj u) (insert u vis)
      ⟨s.visited, u :: s.finished⟩ := by
  simp [visit, hu, foldEmpty]

private theorem visit_nil_struct {V : Type*} [DecidableEq V] (adj : V → List V) :
    ∀ (k : ℕ) (u : V) (vis : Finset V),
      let s := visit adj k u ⟨vis, []⟩
      s.finished.Nodup ∧ (∀ x ∈ s.finished, x ∉ vis) ∧
        (∀ x, x ∈ s.visited ↔ x ∈ vis ∨ x ∈ s.finished)
  | 0, _, vis => ⟨List.nodup_nil, by simp [visit], by simp [visit]⟩
  | k + 1, u, vis => by
    by_cases hu : u ∈ vis
    · simp [visit, hu]
    · have hfold : ∀ (es : List V) (v₀ : Finset V),
          let t := foldEmpty adj k es v₀
          t.finished.Nodup ∧ (∀ x ∈ t.finished, x ∉ v₀) ∧
            (∀ x, x ∈ t.visited ↔ x ∈ v₀ ∨ x ∈ t.finished) := by
        intro es
        induction es with
        | nil => intro v₀; exact ⟨List.nodup_nil, by simp [foldEmpty], by simp [foldEmpty]⟩
        | cons w es ih =>
          intro v₀
          obtain ⟨hnd₁, hdis₁, hvis₁⟩ := visit_nil_struct adj k w v₀
          obtain ⟨hnd₂, hdis₂, hvis₂⟩ := ih (visit adj k w ⟨v₀, []⟩).visited
          rw [foldEmpty_cons]
          dsimp only
          refine ⟨List.nodup_append.2 ⟨hnd₂, hnd₁, fun x hx₂ y hx₁ hxy => ?_⟩,
            fun x hx => ?_, fun x => ?_⟩
          · subst hxy
            exact hdis₂ x hx₂ ((hvis₁ x).2 (.inr hx₁))
          · rcases List.mem_append.1 hx with hx₂ | hx₁
            · exact fun hv => hdis₂ x hx₂ ((hvis₁ x).2 (.inl hv))
            · exact hdis₁ x hx₁
          · rw [hvis₂ x, hvis₁ x, List.mem_append]
            tauto
      obtain ⟨hnd, hdis, hvis⟩ := hfold (adj u) (insert u vis)
      rw [visit_eq_foldEmpty hu]
      dsimp only
      refine ⟨List.nodup_cons.2 ⟨fun hmem => hdis u hmem (Finset.mem_insert_self u vis), hnd⟩,
        fun x hx => ?_, fun x => ?_⟩
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact hu
        · exact fun hv => hdis x hx (Finset.mem_insert_of_mem hv)
      · rw [hvis x, Finset.mem_insert, List.mem_cons]
        tauto

private theorem card_visit_nil {V : Type*} [DecidableEq V] (adj : V → List V)
    (k : ℕ) (u : V) (vis : Finset V) :
    (visit adj k u ⟨vis, []⟩).visited.card =
      vis.card + (visit adj k u ⟨vis, []⟩).finished.length := by
  obtain ⟨hnd, hdis, hvis⟩ := visit_nil_struct adj k u vis
  have hdisj : Disjoint vis (visit adj k u ⟨vis, []⟩).finished.toFinset :=
    Finset.disjoint_right.2 fun x hx => hdis x (List.mem_toFinset.1 hx)
  have hunion : (visit adj k u ⟨vis, []⟩).visited =
      vis ∪ (visit adj k u ⟨vis, []⟩).finished.toFinset := by
    ext x
    simp [hvis x]
  rw [hunion, Finset.card_union_of_disjoint hdisj, List.toFinset_card_of_nodup hnd]

/-- The visited flags at `visAddr` encode the set `vis`. -/
private def VisAt {N : ℕ} (vis : Finset (Fin N)) (visAddr : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ w : Fin N, mem (visAddr + w.val) = (decide (w ∈ vis)).toNat

/-- Register invariant of the depth-first search: constants and array bases. -/
structure DfsRegs (offAddr edgeAddr visAddr finAddr stkAddr : ℕ) (x : Data 28) : Prop where
  czero : x.regs cZero = 0
  cone : x.regs cOne = 1
  cthree : x.regs cThree = 3
  hoff : x.regs offB = offAddr
  hedge : x.regs edgeB = edgeAddr
  hvis : x.regs visB = visAddr
  hfin : x.regs finB = finAddr
  hstk : x.regs stkB = stkAddr

private theorem dfsRegs_of_frame {offAddr edgeAddr visAddr finAddr stkAddr : ℕ} {x y : Data 28}
    (hx : DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x)
    (hfr : ∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r) :
    DfsRegs offAddr edgeAddr visAddr finAddr stkAddr y :=
  { czero := (hfr cZero (by decide)).trans hx.czero
    cone := (hfr cOne (by decide)).trans hx.cone
    cthree := (hfr cThree (by decide)).trans hx.cthree
    hoff := (hfr offB (by decide)).trans hx.hoff
    hedge := (hfr edgeB (by decide)).trans hx.hedge
    hvis := (hfr visB (by decide)).trans hx.hvis
    hfin := (hfr finB (by decide)).trans hx.hfin
    hstk := (hfr stkB (by decide)).trans hx.hstk }

/-- Push the root `uReg` as the first DFS stack frame. -/
private def dfsPushRoot : Code .standard 28 := ram[
  *addr ← cOne;
  addr ← offB + uReg; jReg ← *addr;
  addr ← addr + cOne; jEndReg ← *addr;
  *stkB ← uReg;
  addr ← stkB + cOne; *addr ← jReg;
  addr ← addr + cOne; *addr ← jEndReg;
  pReg ← cOne ]

/-- One DFS step on the top stack frame: pop and finish, skip a visited successor, or push an
unvisited one. -/
private def dfsStepBody : Code .standard 28 := ram[
  vReg ← pReg - cOne;
  addr ← cThree * vReg; addr ← stkB + addr;
  uReg ← *addr;
  addr ← addr + cOne; jReg ← *addr;
  addr ← addr + cOne; jEndReg ← *addr;
  if jReg < jEndReg then [
    addr ← cThree * vReg; addr ← stkB + addr; addr ← addr + cOne;
    jEndReg ← jReg + cOne; *addr ← jEndReg;
    addr ← edgeB + jReg; vReg ← *addr;
    addr ← visB + vReg; jReg ← *addr;
    if jReg = cZero then [
      *addr ← cOne;
      addr ← offB + vReg; jReg ← *addr;
      addr ← addr + cOne; jEndReg ← *addr;
      addr ← cThree * pReg; addr ← stkB + addr;
      *addr ← vReg;
      addr ← addr + cOne; *addr ← jReg;
      addr ← addr + cOne; *addr ← jEndReg;
      pReg ← pReg + cOne ]
    else [ pReg ← pReg ] ]
  else [
    pReg ← vReg;
    addr ← finB + finCnt; *addr ← uReg;
    finCnt ← finCnt + cOne ] ]

/-- Run DFS steps while the stack is nonempty. -/
private def dfsLoop : Code .standard 28 :=
  .loop (.lt cZero pReg) dfsStepBody

/-- Visit the root `uReg` if it is unvisited, running the DFS loop from it. -/
private def visitRootCode : Code .standard 28 := ram[
  addr ← visB + uReg; jReg ← *addr;
  if jReg = cZero then [
    ⟪dfsPushRoot.seq dfsLoop⟫ ]
  else [ pReg ← cZero ] ]

/-- Instruction budget of the DFS loop on the remaining successors `es` of a frame, given the
vertices `new` finished during it. -/
private def dfsFrameTime {N : ℕ} (adj : Fin N → List (Fin N)) (es new : List (Fin N)) : ℕ :=
  20 + 36 * es.length + 60 * new.length + 36 * outDegreeSum adj new

private theorem visAt_insert {N : ℕ} {vis : Finset (Fin N)} {visAddr : ℕ} {mem : ℕ → ℕ}
    (h : VisAt vis visAddr mem) (v : Fin N) :
    VisAt (insert v vis) visAddr (Function.update mem (visAddr + v.val) 1) := by
  intro w
  by_cases hw : w = v
  · subst hw; simp
  · have hne : visAddr + w.val ≠ visAddr + v.val := fun heq => hw (Fin.ext (by omega))
    rw [Function.update_of_ne hne, h w]
    simp [hw]

private theorem dfsStepBody_pop {N w : ℕ} (adj : Fin N → List (Fin N))
    (offAddr edgeAddr visAddr finAddr stkAddr Mc : ℕ)
    (hdisj1 : offAddr + N + 1 ≤ visAddr)
    (hdisj2 : edgeAddr + Mc ≤ visAddr)
    (hdisj3 : visAddr + N ≤ finAddr)
    (hdisj4 : finAddr + N ≤ stkAddr)
    (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (stkAddr + 3 * N + Mc + 4))
    (u : Fin N) (idx d F₀ : ℕ) (vis : Finset (Fin N)) {x : Data 28}
    (hidx : idx = (adj u).length)
    (hcons : F₀ + d + 1 + (N - vis.card) ≤ N)
    (hregs : DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x)
    (hcsr : CSRAt adj offAddr edgeAddr x.mem)
    (hvis : VisAt vis visAddr x.mem)
    (hp : x.regs pReg = d + 1)
    (hfc : x.regs finCnt = F₀)
    (hstk0 : x.mem (stkAddr + 3 * d) = u.val)
    (hstk1 : x.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + idx)
    (hstk2 : x.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1)) :
    ∃ x₁, ExecWithin w dfsStepBody x x₁ 16 ∧
      DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x₁ ∧
      CSRAt adj offAddr edgeAddr x₁.mem ∧
      VisAt vis visAddr x₁.mem ∧
      x₁.regs pReg = d ∧
      x₁.regs finCnt = F₀ + 1 ∧
      x₁.mem (finAddr + F₀) = u.val ∧
      (∀ a, ¬ (a = finAddr + F₀) → x₁.mem a = x.mem a) ∧
      (∀ r : Fin 28, (r.val < 19 ∨ r = compIdxReg ∨ r = oldFinReg) → x₁.regs r = x.regs r) := by
  have hoff_u := csrOffset_succ adj u.isLt
  simp only [Fin.eta] at hoff_u
  have hjeq : csrOffset adj u.val + idx = csrOffset adj (u.val + 1) := by omega
  have hstk1' : x.mem (stkAddr + 3 * d + 1) = csrOffset adj (u.val + 1) := hstk1.trans hjeq
  have hu_lt := u.isLt
  have hf_3d : Fits w (3 * d) := hfit.of_le (by omega)
  have hf_s0 : Fits w (stkAddr + 3 * d) := hfit.of_le (by omega)
  have hf_s1 : Fits w (stkAddr + 3 * d + 1) := hfit.of_le (by omega)
  have hf_s2 : Fits w (stkAddr + 3 * d + 1 + 1) := hfit.of_le (by omega)
  have hf_fin : Fits w (finAddr + F₀) := hfit.of_le (by omega)
  have hf_fc1 : Fits w (F₀ + 1) := hfit.of_le (by omega)
  let PopPost (x₁ : Data 28) : Prop :=
    DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x₁ ∧
      CSRAt adj offAddr edgeAddr x₁.mem ∧
      VisAt vis visAddr x₁.mem ∧
      x₁.regs pReg = d ∧
      x₁.regs finCnt = F₀ + 1 ∧
      x₁.mem (finAddr + F₀) = u.val ∧
      (∀ a, ¬ (a = finAddr + F₀) → x₁.mem a = x.mem a) ∧
      (∀ r : Fin 28, (r.val < 19 ∨ r = compIdxReg ∨ r = oldFinReg) → x₁.regs r = x.regs r)
  change ∃ x₁, ExecWithin w dfsStepBody x x₁ 16 ∧ PopPost x₁
  have hstk2' : x.mem (stkAddr + 3 * d + 1 + 1) = csrOffset adj (u.val + 1) := by
    simpa [Nat.add_assoc] using hstk2
  unfold dfsStepBody
  wram_exec [hregs.czero, hregs.cone, hregs.cthree, hregs.hoff, hregs.hedge, hregs.hvis,
    hregs.hfin, hregs.hstk, hp, hfc, hstk0, hstk1', hstk2',
    hf_3d, hf_s0, hf_s1, hf_s2, hf_fin, hf_fc1]
  dsimp only [PopPost]
  refine ⟨?_, ?_, ?_, by wram_simp, by wram_simp, ?_, fun a ha => ?_, fun r hr => ?_⟩
  · refine dfsRegs_of_frame hregs fun r hr => ?_
    regs_lt
  · mem_upd
    exact hcsr.of_eqOn
      (fun _ _ => Function.update_of_ne (by omega) _ _)
      (fun _ _ => Function.update_of_ne (by omega) _ _)
  · intro w_v; mem_upd
    rw [Function.update_of_ne (by have := w_v.isLt; omega)]; exact hvis w_v
  · mem_upd; exact Function.update_self _ _ _
  · mem_upd; exact Function.update_of_ne ha _ _
  · have hv : r ≠ vReg := by reg_ne
    have ha : r ≠ addr := by reg_ne
    have hu' : r ≠ uReg := by reg_ne
    have hj : r ≠ jReg := by reg_ne
    have hje : r ≠ jEndReg := by reg_ne
    have hp' : r ≠ pReg := by reg_ne
    have hfc' : r ≠ finCnt := by reg_ne
    simp only [Data.write_regs_apply, Data.set_regs_of_ne hv, Data.set_regs_of_ne ha,
      Data.set_regs_of_ne hu', Data.set_regs_of_ne hj, Data.set_regs_of_ne hje,
      Data.set_regs_of_ne hp', Data.set_regs_of_ne hfc']

private theorem dfsStepBody_skip {N w : ℕ} (adj : Fin N → List (Fin N))
    (offAddr edgeAddr visAddr finAddr stkAddr Mc : ℕ)
    (hdisj1 : offAddr + N + 1 ≤ visAddr)
    (hdisj2 : edgeAddr + Mc ≤ visAddr)
    (hdisj3 : visAddr + N ≤ finAddr)
    (hdisj4 : finAddr + N ≤ stkAddr)
    (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (stkAddr + 3 * N + Mc + 4))
    (u v : Fin N) (idx d F₀ : ℕ) (vis : Finset (Fin N)) {x : Data 28}
    (hidx_lt : idx < (adj u).length)
    (hv_eq : (adj u)[idx]'hidx_lt = v)
    (hmem : v ∈ vis)
    (hcons : F₀ + d + 1 + (N - vis.card) ≤ N)
    (hregs : DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x)
    (hcsr : CSRAt adj offAddr edgeAddr x.mem)
    (hvis : VisAt vis visAddr x.mem)
    (hp : x.regs pReg = d + 1)
    (hfc : x.regs finCnt = F₀)
    (hstk0 : x.mem (stkAddr + 3 * d) = u.val)
    (hstk1 : x.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + idx)
    (hstk2 : x.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1)) :
    ∃ x₁, ExecWithin w dfsStepBody x x₁ 24 ∧
      DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x₁ ∧
      CSRAt adj offAddr edgeAddr x₁.mem ∧
      VisAt vis visAddr x₁.mem ∧
      x₁.regs pReg = d + 1 ∧
      x₁.regs finCnt = F₀ ∧
      x₁.mem (stkAddr + 3 * d) = u.val ∧
      x₁.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + (idx + 1) ∧
      x₁.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1) ∧
      (∀ a, a ≠ stkAddr + 3 * d + 1 → x₁.mem a = x.mem a) ∧
      (∀ r : Fin 28, (r.val < 19 ∨ r = compIdxReg ∨ r = oldFinReg) → x₁.regs r = x.regs r) := by
  have hoff_u := csrOffset_succ adj u.isLt
  simp only [Fin.eta] at hoff_u
  set j := csrOffset adj u.val + idx
  have hj_lt_end : j < csrOffset adj (u.val + 1) := by omega
  have hj_lt_N : j < csrOffset adj N :=
    lt_of_lt_of_le hj_lt_end (csrOffset_mono adj (by have := u.isLt; omega : u.val + 1 ≤ N))
  have hedge_j : x.mem (edgeAddr + j) = v.val := by
    rw [show edgeAddr + j = edgeAddr + csrOffset adj u.val + idx by dsimp only [j]; omega,
      hcsr.2 u idx hidx_lt, hv_eq]
  have hvis_v1 : x.mem (visAddr + v.val) = 1 := by simpa [hmem] using hvis v
  have hu_lt := u.isLt
  have hv_lt := v.isLt
  have hf_3d : Fits w (3 * d) := hfit.of_le (by omega)
  have hf_s0 : Fits w (stkAddr + 3 * d) := hfit.of_le (by omega)
  have hf_s1 : Fits w (stkAddr + 3 * d + 1) := hfit.of_le (by omega)
  have hf_s2 : Fits w (stkAddr + 3 * d + 1 + 1) := hfit.of_le (by omega)
  have hf_j1 : Fits w (j + 1) := hfit.of_le (by omega)
  have hf_ej : Fits w (edgeAddr + j) := hfit.of_le (by omega)
  have hf_vv : Fits w (visAddr + v.val) := hfit.of_le (by omega)
  have hstk2' : x.mem (stkAddr + 3 * d + 1 + 1) = csrOffset adj (u.val + 1) := by
    simpa [Nat.add_assoc] using hstk2
  let SkipPost (x₁ : Data 28) : Prop :=
    DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x₁ ∧
      CSRAt adj offAddr edgeAddr x₁.mem ∧
      VisAt vis visAddr x₁.mem ∧
      x₁.regs pReg = d + 1 ∧
      x₁.regs finCnt = F₀ ∧
      x₁.mem (stkAddr + 3 * d) = u.val ∧
      x₁.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + (idx + 1) ∧
      x₁.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1) ∧
      (∀ a, a ≠ stkAddr + 3 * d + 1 → x₁.mem a = x.mem a) ∧
      (∀ r : Fin 28, (r.val < 19 ∨ r = compIdxReg ∨ r = oldFinReg) → x₁.regs r = x.regs r)
  change ∃ x₁, ExecWithin w dfsStepBody x x₁ 24 ∧ SkipPost x₁
  unfold dfsStepBody
  wram_exec [hregs.czero, hregs.cone, hregs.cthree, hregs.hoff, hregs.hedge, hregs.hvis,
    hregs.hfin, hregs.hstk, hp, hfc, hstk0, hstk1, hstk2', hedge_j, hvis_v1, hj_lt_end,
    hf_3d, hf_s0, hf_s1, hf_s2, hf_j1, hf_ej, hf_vv]
  dsimp only [SkipPost]
  refine ⟨?_, ?_, ?_, by wram_simp, by wram_simp; exact hfc, ?_, ?_, ?_,
    fun a ha => ?_, fun r hr => ?_⟩
  · refine dfsRegs_of_frame hregs fun r hr => ?_
    regs_lt
  · mem_upd
    exact hcsr.of_eqOn
      (fun _ _ => Function.update_of_ne (by omega) _ _)
      (fun _ _ => Function.update_of_ne (by omega) _ _)
  · intro w_v; mem_upd
    rw [Function.update_of_ne (by have := w_v.isLt; omega)]; exact hvis w_v
  · mem_upd; rw [Function.update_of_ne (by omega)]; exact hstk0
  · mem_upd; rw [Function.update_self]; omega
  · mem_upd; rw [Function.update_of_ne (by omega)]; exact hstk2
  · mem_upd; exact Function.update_of_ne ha _ _
  · have hv : r ≠ vReg := by reg_ne
    have ha : r ≠ addr := by reg_ne
    have hu' : r ≠ uReg := by reg_ne
    have hj : r ≠ jReg := by reg_ne
    have hje : r ≠ jEndReg := by reg_ne
    have hp' : r ≠ pReg := by reg_ne
    simp only [Data.write_regs_apply, Data.set_regs_of_ne hv, Data.set_regs_of_ne ha,
      Data.set_regs_of_ne hu', Data.set_regs_of_ne hj, Data.set_regs_of_ne hje,
      Data.set_regs_of_ne hp']

private theorem dfsStepBody_push {N w : ℕ} (adj : Fin N → List (Fin N))
    (offAddr edgeAddr visAddr finAddr stkAddr Mc : ℕ)
    (hdisj1 : offAddr + N + 1 ≤ visAddr)
    (hdisj2 : edgeAddr + Mc ≤ visAddr)
    (hdisj3 : visAddr + N ≤ finAddr)
    (hdisj4 : finAddr + N ≤ stkAddr)
    (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (stkAddr + 3 * N + Mc + 4))
    (u v : Fin N) (idx d F₀ : ℕ) (vis : Finset (Fin N)) {x : Data 28}
    (hidx_lt : idx < (adj u).length)
    (hv_eq : (adj u)[idx]'hidx_lt = v)
    (hmem : v ∉ vis)
    (hcons_child : F₀ + (d + 1) + 1 + (N - (insert v vis).card) ≤ N)
    (hregs : DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x)
    (hcsr : CSRAt adj offAddr edgeAddr x.mem)
    (hvis : VisAt vis visAddr x.mem)
    (hp : x.regs pReg = d + 1)
    (hfc : x.regs finCnt = F₀)
    (hstk0 : x.mem (stkAddr + 3 * d) = u.val)
    (hstk1 : x.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + idx)
    (hstk2 : x.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1)) :
    ∃ x₁, ExecWithin w dfsStepBody x x₁ 34 ∧
      DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x₁ ∧
      CSRAt adj offAddr edgeAddr x₁.mem ∧
      VisAt (insert v vis) visAddr x₁.mem ∧
      x₁.regs pReg = (d + 1) + 1 ∧
      x₁.regs finCnt = F₀ ∧
      x₁.mem (stkAddr + 3 * d) = u.val ∧
      x₁.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + (idx + 1) ∧
      x₁.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1) ∧
      x₁.mem (stkAddr + 3 * (d + 1)) = v.val ∧
      x₁.mem (stkAddr + 3 * (d + 1) + 1) = csrOffset adj v.val + 0 ∧
      x₁.mem (stkAddr + 3 * (d + 1) + 2) = csrOffset adj (v.val + 1) ∧
      (∀ a, ¬ (a = visAddr + v.val ∨
          (stkAddr + 3 * d ≤ a ∧ a < stkAddr + 3 * N)) → x₁.mem a = x.mem a) ∧
      (∀ r : Fin 28, (r.val < 19 ∨ r = compIdxReg ∨ r = oldFinReg) → x₁.regs r = x.regs r) := by
  have hoff_u := csrOffset_succ adj u.isLt
  simp only [Fin.eta] at hoff_u
  set j := csrOffset adj u.val + idx
  have hj_lt_end : j < csrOffset adj (u.val + 1) := by omega
  have hj_lt_N : j < csrOffset adj N :=
    lt_of_lt_of_le hj_lt_end (csrOffset_mono adj (by have := u.isLt; omega : u.val + 1 ≤ N))
  have hedge_j : x.mem (edgeAddr + j) = v.val := by
    rw [show edgeAddr + j = edgeAddr + csrOffset adj u.val + idx by dsimp only [j]; omega,
      hcsr.2 u idx hidx_lt, hv_eq]
  have hvis_v0 : x.mem (visAddr + v.val) = 0 := by simpa [hmem] using hvis v
  set vis₁ := insert v vis
  have hcard_vis₁_le : vis₁.card ≤ N := by
    have := Finset.card_le_univ vis₁; simpa using this
  have hu_lt := u.isLt
  have hv_lt := v.isLt
  have hoff_v0 : x.mem (offAddr + v.val) = csrOffset adj v.val := hcsr.1 v.val (by omega)
  have hoff_v1 : x.mem (offAddr + v.val + 1) = csrOffset adj (v.val + 1) := by
    simpa [Nat.add_assoc] using hcsr.1 (v.val + 1) (by omega)
  have hf_3d : Fits w (3 * d) := hfit.of_le (by omega)
  have hf_s0 : Fits w (stkAddr + 3 * d) := hfit.of_le (by omega)
  have hf_s1 : Fits w (stkAddr + 3 * d + 1) := hfit.of_le (by omega)
  have hf_s2 : Fits w (stkAddr + 3 * d + 1 + 1) := hfit.of_le (by omega)
  have hf_j1 : Fits w (j + 1) := hfit.of_le (by omega)
  have hf_ej : Fits w (edgeAddr + j) := hfit.of_le (by omega)
  have hf_vv : Fits w (visAddr + v.val) := hfit.of_le (by omega)
  have hf_ov0 : Fits w (offAddr + v.val) := hfit.of_le (by omega)
  have hf_ov1 : Fits w (offAddr + v.val + 1) := hfit.of_le (by omega)
  have hf_3d1 : Fits w (3 * (d + 1)) := hfit.of_le (by omega)
  have hf_c0 : Fits w (stkAddr + 3 * (d + 1)) := hfit.of_le (by omega)
  have hf_c1 : Fits w (stkAddr + 3 * (d + 1) + 1) := hfit.of_le (by omega)
  have hf_c2 : Fits w (stkAddr + 3 * (d + 1) + 1 + 1) := hfit.of_le (by omega)
  have hf_p2 : Fits w (d + 1 + 1) := hfit.of_le (by omega)
  have hstk2' : x.mem (stkAddr + 3 * d + 1 + 1) = csrOffset adj (u.val + 1) := by
    simpa [Nat.add_assoc] using hstk2
  let PushPost (x₁ : Data 28) : Prop :=
    DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x₁ ∧
      CSRAt adj offAddr edgeAddr x₁.mem ∧
      VisAt vis₁ visAddr x₁.mem ∧
      x₁.regs pReg = (d + 1) + 1 ∧
      x₁.regs finCnt = F₀ ∧
      x₁.mem (stkAddr + 3 * d) = u.val ∧
      x₁.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + (idx + 1) ∧
      x₁.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1) ∧
      x₁.mem (stkAddr + 3 * (d + 1)) = v.val ∧
      x₁.mem (stkAddr + 3 * (d + 1) + 1) = csrOffset adj v.val + 0 ∧
      x₁.mem (stkAddr + 3 * (d + 1) + 2) = csrOffset adj (v.val + 1) ∧
      (∀ a, ¬ (a = visAddr + v.val ∨
          (stkAddr + 3 * d ≤ a ∧ a < stkAddr + 3 * N)) → x₁.mem a = x.mem a) ∧
      (∀ r : Fin 28, (r.val < 19 ∨ r = compIdxReg ∨ r = oldFinReg) → x₁.regs r = x.regs r)
  change ∃ x₁, ExecWithin w dfsStepBody x x₁ 34 ∧ PushPost x₁
  unfold dfsStepBody
  wram_exec [hregs.czero, hregs.cone, hregs.cthree, hregs.hoff, hregs.hedge, hregs.hvis,
    hregs.hfin, hregs.hstk, hp, hfc, hstk0, hstk1, hstk2', hedge_j, hvis_v0, hj_lt_end,
    hoff_v0, hoff_v1, hf_3d, hf_s0, hf_s1, hf_s2, hf_j1, hf_ej, hf_vv,
    hf_ov0, hf_ov1, hf_3d1, hf_c0, hf_c1, hf_c2, hf_p2]
  dsimp only [PushPost]
  refine ⟨?_, ?_, ?_, by wram_simp, by wram_simp; exact hfc,
    ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, fun r hr => ?_⟩
  · refine dfsRegs_of_frame hregs fun r hr => ?_
    regs_lt
  · mem_upd
    exact hcsr.of_eqOn
      (fun _ _ => by repeat rw [Function.update_of_ne (by omega)])
      (fun _ _ => by repeat rw [Function.update_of_ne (by omega)])
  · intro w_v; mem_upd
    have hw_lt := w_v.isLt
    repeat rw [Function.update_of_ne (by omega)]
    by_cases hwv : w_v = v
    · subst hwv
      rw [Function.update_self]
      simp [vis₁]
    · have hne : visAddr + w_v.val ≠ visAddr + v.val := fun h => hwv (Fin.ext (by omega))
      rw [Function.update_of_ne hne, Function.update_of_ne (by omega)]
      simpa [vis₁, hwv] using hvis w_v
  · mem_upd; repeat rw [Function.update_of_ne (by omega)]
    exact hstk0
  · mem_upd; repeat rw [Function.update_of_ne (by omega)]
    rw [Function.update_self]; omega
  · mem_upd; repeat rw [Function.update_of_ne (by omega)]
    exact hstk2
  · mem_upd
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  · mem_upd
    rw [Function.update_of_ne (by omega), Function.update_self]; omega
  · mem_upd
    rw [show stkAddr + 3 * (d + 1) + 2 = stkAddr + 3 * (d + 1) + 1 + 1 by omega,
      Function.update_self]
  · mem_upd
    repeat rw [Function.update_of_ne (by omega)]
  · have hv : r ≠ vReg := by reg_ne
    have ha : r ≠ addr := by reg_ne
    have hu' : r ≠ uReg := by reg_ne
    have hj : r ≠ jReg := by reg_ne
    have hje : r ≠ jEndReg := by reg_ne
    have hp' : r ≠ pReg := by reg_ne
    simp only [Data.write_regs_apply, Data.set_regs_of_ne hv, Data.set_regs_of_ne ha,
      Data.set_regs_of_ne hu', Data.set_regs_of_ne hj, Data.set_regs_of_ne hje,
      Data.set_regs_of_ne hp']

private theorem dfsLoop_cps {N w : ℕ} (adj : Fin N → List (Fin N))
    (offAddr edgeAddr visAddr finAddr stkAddr Mc : ℕ)
    (hdisj1 : offAddr + N + 1 ≤ visAddr)
    (hdisj2 : edgeAddr + Mc ≤ visAddr)
    (hdisj3 : visAddr + N ≤ finAddr)
    (hdisj4 : finAddr + N ≤ stkAddr)
    (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (stkAddr + 3 * N + Mc + 4)) :
    ∀ (k : ℕ),
      ∀ (u : Fin N) (es : List (Fin N)) (idx d F₀ T_cont : ℕ)
        (vis : Finset (Fin N)) (x : Data 28) (Q : Data 28 → Prop)
        (_ : idx + es.length = (adj u).length),
        (∀ q (hq : q < es.length),
          (adj u)[idx + q]'(by omega) = es[q]) →
        N - vis.card ≤ k →
        F₀ + d + 1 + (N - vis.card) ≤ N →
        DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x →
        CSRAt adj offAddr edgeAddr x.mem →
        VisAt vis visAddr x.mem →
        x.regs pReg = d + 1 →
        x.regs finCnt = F₀ →
        x.mem (stkAddr + 3 * d) = u.val →
        x.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + idx →
        x.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1) →
        (∀ y : Data 28,
          let s := foldEmpty adj k es vis
          DfsRegs offAddr edgeAddr visAddr finAddr stkAddr y →
          CSRAt adj offAddr edgeAddr y.mem →
          VisAt s.visited visAddr y.mem →
          y.regs pReg = d →
          y.regs finCnt = F₀ + s.finished.length + 1 →
          (∀ q (hq : q < s.finished.reverse.length),
            y.mem (finAddr + F₀ + q) = (s.finished.reverse[q]).val) →
          y.mem (finAddr + F₀ + s.finished.length) = u.val →
          (∀ a, ¬ ((visAddr ≤ a ∧ a < visAddr + N) ∨
              (finAddr + F₀ ≤ a ∧ a < finAddr + F₀ + s.finished.length + 1) ∨
              (stkAddr + 3 * d ≤ a ∧ a < stkAddr + 3 * N)) → y.mem a = x.mem a) →
          (∀ r : Fin 28, (r.val < 19 ∨ r = compIdxReg ∨ r = oldFinReg) → y.regs r = x.regs r) →
          ∃ z, ExecWithin w dfsLoop y z T_cont ∧ Q z) →
        ∃ z, ExecWithin w dfsLoop x z
          (dfsFrameTime adj es (foldEmpty adj k es vis).finished + T_cont) ∧ Q z := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih_k =>
    intro u es
    induction es with
    | nil =>
      intro idx d F₀ T_cont vis x Q hidx _ _ hcons hregs hcsr hvis hp hfc hstk0 hstk1 hstk2 hcont
      simp only [List.length_nil, Nat.add_zero] at hidx
      obtain ⟨x₁, ⟨t₁, ht₁, he₁⟩, hx₁_r, hx₁_csr, hx₁_vis, hx₁_p, hx₁_fc, hx₁_fin0, hx₁_out,
        hx₁_fr⟩ :=
        dfsStepBody_pop adj offAddr edgeAddr visAddr finAddr stkAddr Mc
          hdisj1 hdisj2 hdisj3 hdisj4 hmc hfit u idx d F₀ vis hidx hcons
          hregs hcsr hvis hp hfc hstk0 hstk1 hstk2
      obtain ⟨z, ⟨t₂, ht₂, he₂⟩, hQz⟩ := hcont x₁ hx₁_r hx₁_csr hx₁_vis hx₁_p
        (by simpa [foldEmpty] using hx₁_fc)
        (fun q hq => by simp [foldEmpty] at hq)
        (by simpa [foldEmpty] using hx₁_fin0)
        (fun a ha => hx₁_out a (by dsimp only [foldEmpty, List.length_nil] at ha; omega))
        hx₁_fr
      have hlt : (Cond.lt cZero pReg).Holds x := by
        have := hregs.czero
        change x.regs cZero < x.regs pReg; omega
      exact ⟨z, ⟨t₁ + t₂ + 2, by dsimp only [dfsFrameTime, foldEmpty, outDegreeSum]; omega,
        Exec.loop_iter hlt he₁ he₂⟩, hQz⟩
    | cons v es' ih_es =>
      intro idx d F₀ T_cont vis x Q hidx hes hk hcons hregs hcsr hvis hp hfc hstk0 hstk1 hstk2
        hcont
      simp only [List.length_cons] at hidx
      have hv_eq : (adj u)[idx]'(by omega) = v := by
        have h0 := hes 0 (by simp)
        simpa only [Nat.add_zero, List.getElem_cons_zero] using h0
      have hes' : ∀ q (hq : q < es'.length), (adj u)[idx + 1 + q]'(by omega) = es'[q] := by
        intro q hq
        have h := hes (q + 1) (by simp only [List.length_cons]; omega)
        have hcongr : (adj u)[idx + 1 + q]'(by omega) = (adj u)[idx + (q + 1)]'(by omega) := by
          congr 1; omega
        exact hcongr.trans (by simpa only [List.getElem_cons_succ] using h)
      by_cases hmem : v ∈ vis
      · -- Case 1: `v ∈ vis`
        have hvisit_v : visit adj k v ⟨vis, []⟩ = ⟨vis, []⟩ := by
          cases k with
          | zero => rfl
          | succ k' => exact visit_of_mem hmem
        have hfold_eq : foldEmpty adj k (v :: es') vis = foldEmpty adj k es' vis := by
          rw [foldEmpty_cons, hvisit_v]
          simp
        obtain ⟨x₁, ⟨t₁, ht₁, he₁⟩, hx₁_r, hx₁_csr, hx₁_vis, hx₁_p, hx₁_fc, hx₁_s0, hx₁_s1,
          hx₁_s2, hx₁_out, hx₁_fr⟩ :=
          dfsStepBody_skip adj offAddr edgeAddr visAddr finAddr stkAddr Mc
            hdisj1 hdisj2 hdisj3 hdisj4 hmc hfit u v idx d F₀ vis (by omega) hv_eq hmem hcons
            hregs hcsr hvis hp hfc hstk0 hstk1 hstk2
        obtain ⟨z, ⟨t₂, ht₂, he₂⟩, hQz⟩ := ih_es (idx + 1) d F₀ T_cont vis x₁ Q (by omega) hes'
          hk hcons hx₁_r hx₁_csr hx₁_vis hx₁_p hx₁_fc hx₁_s0 hx₁_s1 hx₁_s2
          (fun y hy_r hy_csr hy_vis hy_p hy_fc hy_fin hy_u hy_out hy_fr => by
            rw [hfold_eq] at hcont
            exact hcont y hy_r hy_csr hy_vis hy_p hy_fc hy_fin hy_u
              (fun a ha => (hy_out a ha).trans (hx₁_out a (by omega)))
              (fun r hr => (hy_fr r hr).trans (hx₁_fr r hr)))
        have hlt : (Cond.lt cZero pReg).Holds x := by
          have := hregs.czero
          change x.regs cZero < x.regs pReg; omega
        refine ⟨z, ⟨t₁ + t₂ + 2, ?_, Exec.loop_iter hlt he₁ he₂⟩, hQz⟩
        rw [hfold_eq]
        simp only [dfsFrameTime, List.length_cons] at ht₂ ⊢
        omega
      · -- Case 2: `v ∉ vis`
        have hcard_lt : vis.card < N := by simpa using Finset.card_lt_univ_of_notMem hmem
        rcases k with _ | k'
        · omega
        set vis₁ := insert v vis
        have hcard_vis₁ : vis₁.card = vis.card + 1 := Finset.card_insert_of_notMem hmem
        have hcard_vis₁_le : vis₁.card ≤ N := by
          have := Finset.card_le_univ vis₁; simpa using this
        have hk' : N - vis₁.card ≤ k' := by omega
        have hcons_child : F₀ + (d + 1) + 1 + (N - vis₁.card) ≤ N := by omega
        obtain ⟨x₁, ⟨t₁, ht₁, he₁⟩, hx₁_r, hx₁_csr, hx₁_vis, hx₁_p, hx₁_fc, hx₁_d0, hx₁_d1,
          hx₁_d2, hx₁_c0, hx₁_c1, hx₁_c2, hx₁_out, hx₁_fr⟩ :=
          dfsStepBody_push adj offAddr edgeAddr visAddr finAddr stkAddr Mc
            hdisj1 hdisj2 hdisj3 hdisj4 hmc hfit u v idx d F₀ vis (by omega) hv_eq hmem
            hcons_child hregs hcsr hvis hp hfc hstk0 hstk1 hstk2
        obtain ⟨s₁, hs₁_def⟩ : ∃ s₁, visit adj (k' + 1) v ⟨vis, []⟩ = s₁ := ⟨_, rfl⟩
        obtain ⟨s_child, hsc_def⟩ : ∃ s_child, foldEmpty adj k' (adj v) vis₁ = s_child := ⟨_, rfl⟩
        have hs₁_eq : s₁ = ⟨s_child.visited, v :: s_child.finished⟩ := by
          rw [← hs₁_def, ← hsc_def]; exact visit_eq_foldEmpty hmem
        obtain ⟨s₂, hs₂_def⟩ : ∃ s₂, foldEmpty adj (k' + 1) es' s₁.visited = s₂ := ⟨_, rfl⟩
        have hfold_cons : foldEmpty adj (k' + 1) (v :: es') vis =
            ⟨s₂.visited, s₂.finished ++ s₁.finished⟩ := by
          rw [← hs₂_def, ← hs₁_def]; exact foldEmpty_cons adj (k' + 1) v es' vis
        have hcard_s₁ : s₁.visited.card = vis.card + s₁.finished.length := by
          rw [← hs₁_def]; exact card_visit_nil adj (k' + 1) v vis
        have hcard_s₁_le : s₁.visited.card ≤ N := by
          have := Finset.card_le_univ s₁.visited; simpa only [Fintype.card_fin] using this
        have hlen_s₁ : s₁.finished.length = s_child.finished.length + 1 := by
          rw [hs₁_eq]; rfl
        have hk_s₁ : N - s₁.visited.card ≤ k' + 1 := by omega
        have hcons_after : (F₀ + s₁.finished.length) + d + 1 + (N - s₁.visited.card) ≤ N := by
          omega
        obtain ⟨z, ⟨t₂, ht₂, he₂⟩, hQz⟩ := ih_k k' (Nat.lt_succ_self k') v (adj v) 0 (d + 1) F₀
          (dfsFrameTime adj es' s₂.finished + T_cont) vis₁ x₁ Q (Nat.zero_add _)
          (fun q hq => by simp only [Nat.zero_add]) hk' hcons_child hx₁_r hx₁_csr hx₁_vis hx₁_p
          hx₁_fc hx₁_c0 hx₁_c1 hx₁_c2
          (fun y₁ hy₁_r hy₁_csr hy₁_vis hy₁_p hy₁_fc hy₁_fin hy₁_v hy₁_out hy₁_fr => by
            rw [hsc_def] at hy₁_vis hy₁_fc hy₁_fin hy₁_v hy₁_out
            have hy₁_vis' : VisAt s₁.visited visAddr y₁.mem := by rw [hs₁_eq]; exact hy₁_vis
            have hy₁_fc' : y₁.regs finCnt = F₀ + s₁.finished.length := by
              rw [hlen_s₁]; exact hy₁_fc
            have hy₁_d0 : y₁.mem (stkAddr + 3 * d) = u.val :=
              (hy₁_out (stkAddr + 3 * d) (by omega)).trans hx₁_d0
            have hy₁_d1 : y₁.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + (idx + 1) :=
              (hy₁_out (stkAddr + 3 * d + 1) (by omega)).trans hx₁_d1
            have hy₁_d2 : y₁.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1) :=
              (hy₁_out (stkAddr + 3 * d + 2) (by omega)).trans hx₁_d2
            rw [← hs₂_def]
            exact ih_es (idx + 1) d (F₀ + s₁.finished.length) T_cont s₁.visited y₁ Q
              (by omega) hes' hk_s₁ hcons_after hy₁_r hy₁_csr hy₁_vis' hy₁_p hy₁_fc'
              hy₁_d0 hy₁_d1 hy₁_d2
              (fun y₂ hy₂_r hy₂_csr hy₂_vis hy₂_p hy₂_fc hy₂_fin hy₂_u hy₂_out hy₂_fr => by
                rw [hs₂_def] at hy₂_vis hy₂_fc hy₂_fin hy₂_u hy₂_out
                have hy₂_vis' : VisAt (foldEmpty adj (k' + 1) (v :: es') vis).visited
                    visAddr y₂.mem := by
                  rw [hfold_cons]; exact hy₂_vis
                have hy₂_fc' : y₂.regs finCnt =
                    F₀ + (foldEmpty adj (k' + 1) (v :: es') vis).finished.length + 1 := by
                  rw [hfold_cons]; dsimp only; rw [List.length_append]; omega
                have hy₂_u' : y₂.mem (finAddr + F₀ +
                    (foldEmpty adj (k' + 1) (v :: es') vis).finished.length) = u.val := by
                  rw [hfold_cons]; dsimp only; rw [List.length_append]
                  rw [show finAddr + F₀ + (s₂.finished.length + s₁.finished.length) =
                    finAddr + (F₀ + s₁.finished.length) + s₂.finished.length by omega]
                  exact hy₂_u
                have hy₂_fin_all :
                    ∀ q (hq : q < (foldEmpty adj (k' + 1) (v :: es') vis).finished.reverse.length),
                      y₂.mem (finAddr + F₀ + q) =
                        ((foldEmpty adj (k' + 1) (v :: es') vis).finished.reverse[q]).val := by
                  intro q hq
                  have hrev : (foldEmpty adj (k' + 1) (v :: es') vis).finished.reverse =
                      s_child.finished.reverse ++ [v] ++ s₂.finished.reverse := by
                    rw [hfold_cons, hs₁_eq]
                    simp only [List.reverse_append, List.reverse_cons, List.append_assoc]
                  have hrev2 : (foldEmpty adj (k' + 1) (v :: es') vis).finished.reverse =
                      s₁.finished.reverse ++ s₂.finished.reverse := by
                    rw [hfold_cons]; dsimp only; exact List.reverse_append
                  have hq_tot : q < s_child.finished.length + 1 + s₂.finished.length := by
                    rw [hrev] at hq
                    simp only [List.length_append, List.length_reverse,
                      List.length_singleton] at hq
                    omega
                  by_cases hq1 : q < s_child.finished.length
                  · have hpres : y₂.mem (finAddr + F₀ + q) = y₁.mem (finAddr + F₀ + q) :=
                      hy₂_out (finAddr + F₀ + q) (by omega)
                    rw [hpres, hy₁_fin q (by rw [List.length_reverse]; exact hq1)]
                    congr 1
                    simp only [hrev, List.append_assoc]
                    rw [List.getElem_append_left (by rw [List.length_reverse]; exact hq1)]
                  · by_cases hq2 : q = s_child.finished.length
                    · subst hq2
                      have hpres : y₂.mem (finAddr + F₀ + s_child.finished.length) =
                          y₁.mem (finAddr + F₀ + s_child.finished.length) :=
                        hy₂_out (finAddr + F₀ + s_child.finished.length) (by omega)
                      rw [hpres, hy₁_v]
                      congr 1
                      simp only [hrev, List.append_assoc]
                      rw [List.getElem_append_right (by rw [List.length_reverse])]
                      simp only [List.length_reverse, Nat.sub_self, List.singleton_append,
                        List.getElem_cons_zero]
                    · set q' := q - s₁.finished.length
                      have hq'_lt : q' < s₂.finished.reverse.length := by
                        rw [List.length_reverse]; omega
                      have haddr_eq :
                          finAddr + F₀ + q = finAddr + (F₀ + s₁.finished.length) + q' := by
                        omega
                      rw [haddr_eq, hy₂_fin q' hq'_lt]
                      congr 1
                      simp only [hrev2]
                      have hge : s₁.finished.reverse.length ≤ q := by
                        rw [List.length_reverse]; omega
                      rw [List.getElem_append_right hge]
                      congr 1
                      rw [List.length_reverse]
                exact hcont y₂ hy₂_r hy₂_csr hy₂_vis' hy₂_p hy₂_fc' hy₂_fin_all hy₂_u'
                  (fun a ha => by
                    rw [hfold_cons] at ha; dsimp only at ha
                    rw [List.length_append] at ha
                    have h2 := hy₂_out a (by omega)
                    have h1 := hy₁_out a (by omega)
                    have h0 := hx₁_out a (by have := v.isLt; omega)
                    exact h2.trans (h1.trans h0))
                  (fun r hr => (hy₂_fr r hr).trans ((hy₁_fr r hr).trans (hx₁_fr r hr)))))
        have hlt : (Cond.lt cZero pReg).Holds x := by
          have := hregs.czero
          change x.regs cZero < x.regs pReg; omega
        refine ⟨z, ⟨t₁ + t₂ + 2, ?_, Exec.loop_iter hlt he₁ he₂⟩, hQz⟩
        rw [hsc_def] at ht₂
        have hout_eq : outDegreeSum adj (foldEmpty adj (k' + 1) (v :: es') vis).finished =
            outDegreeSum adj s₂.finished +
              ((adj v).length + outDegreeSum adj s_child.finished) := by
          rw [hfold_cons, hs₁_eq]
          dsimp only
          rw [outDegreeSum_append]
          simp only [outDegreeSum, List.map_cons, List.sum_cons]
        have hlen_eq : (foldEmpty adj (k' + 1) (v :: es') vis).finished.length =
            s₂.finished.length + (1 + s_child.finished.length) := by
          rw [hfold_cons, hs₁_eq]; dsimp only; rw [List.length_append, List.length_cons]; omega
        simp only [dfsFrameTime, List.length_cons, hout_eq, hlen_eq] at ht₂ ⊢
        omega

private theorem visitRootCode_spec {N w : ℕ} (hN : 0 < N) (adj : Fin N → List (Fin N))
    (offAddr edgeAddr visAddr finAddr stkAddr Mc : ℕ)
    (hdisj1 : offAddr + N + 1 ≤ visAddr)
    (hdisj2 : edgeAddr + Mc ≤ visAddr)
    (hdisj3 : visAddr + N ≤ finAddr)
    (hdisj4 : finAddr + N ≤ stkAddr)
    (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (stkAddr + 3 * N + Mc + 4))
    (r : Fin N) (F₀ : ℕ) (vis : Finset (Fin N))
    (hcons : F₀ + (N - vis.card) ≤ N)
    {x : Data 28}
    (hregs : DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x)
    (hcsr : CSRAt adj offAddr edgeAddr x.mem)
    (hvis : VisAt vis visAddr x.mem)
    (hu : x.regs uReg = r.val)
    (hfc : x.regs finCnt = F₀) :
    let s := visit adj N r ⟨vis, []⟩
    ∃ y, ExecWithin w visitRootCode x y
        (16 + 60 * s.finished.length + 36 * outDegreeSum adj s.finished) ∧
      DfsRegs offAddr edgeAddr visAddr finAddr stkAddr y ∧
      CSRAt adj offAddr edgeAddr y.mem ∧
      VisAt s.visited visAddr y.mem ∧
      y.regs finCnt = F₀ + s.finished.length ∧
      (∀ q (hq : q < s.finished.reverse.length),
        y.mem (finAddr + F₀ + q) = (s.finished.reverse[q]).val) ∧
      (∀ a, ¬ ((visAddr ≤ a ∧ a < visAddr + N) ∨
          (finAddr + F₀ ≤ a ∧ a < finAddr + F₀ + s.finished.length) ∨
          (stkAddr ≤ a ∧ a < stkAddr + 3 * N)) → y.mem a = x.mem a) ∧
      (∀ reg : Fin 28, (reg.val < 19 ∨ reg = compIdxReg ∨ reg = oldFinReg) →
        y.regs reg = x.regs reg) := by
  have hr_lt := r.isLt
  have hvis_r : x.mem (visAddr + r.val) = (decide (r ∈ vis)).toNat := hvis r
  have hf_vr : Fits w (visAddr + r.val) := hfit.of_le (by omega)
  obtain ⟨k', hkN⟩ : ∃ k', N = k' + 1 := ⟨N - 1, by omega⟩
  let RootPost (y : Data 28) : Prop :=
    let s := visit adj N r ⟨vis, []⟩
    DfsRegs offAddr edgeAddr visAddr finAddr stkAddr y ∧
      CSRAt adj offAddr edgeAddr y.mem ∧
      VisAt s.visited visAddr y.mem ∧
      y.regs finCnt = F₀ + s.finished.length ∧
      (∀ q (hq : q < s.finished.reverse.length),
        y.mem (finAddr + F₀ + q) = (s.finished.reverse[q]).val) ∧
      (∀ a, ¬ ((visAddr ≤ a ∧ a < visAddr + N) ∨
          (finAddr + F₀ ≤ a ∧ a < finAddr + F₀ + s.finished.length) ∨
          (stkAddr ≤ a ∧ a < stkAddr + 3 * N)) → y.mem a = x.mem a) ∧
      (∀ reg : Fin 28, (reg.val < 19 ∨ reg = compIdxReg ∨ reg = oldFinReg) →
        y.regs reg = x.regs reg)
  change ∃ y, ExecWithin w visitRootCode x y _ ∧ RootPost y
  by_cases hmem : r ∈ vis
  · have hvis_1 : x.mem (visAddr + r.val) = 1 := by simpa [hmem] using hvis_r
    have hs_eq : visit adj N r ⟨vis, []⟩ = ⟨vis, []⟩ :=
      (congrArg (fun fuel => visit adj fuel r ⟨vis, []⟩) hkN).trans (visit_of_mem hmem)
    unfold visitRootCode
    wram_exec [hregs.czero, hregs.hvis, hu, hvis_1, hf_vr]
    dsimp only [RootPost]
    rw [hs_eq]
    refine ⟨?_, ?_, ?_, ?_, fun _ hq => by simp at hq, fun _ _ => rfl, fun reg hreg => ?_⟩
    · refine dfsRegs_of_frame hregs fun reg hreg => ?_
      regs_lt
    · mem_upd; exact hcsr
    · intro w_v; mem_upd; exact hvis w_v
    · wram_simp; simpa using hfc
    · regs_lt
  · have hvis_0 : x.mem (visAddr + r.val) = 0 := by simpa [hmem] using hvis_r
    set vis₁ := insert r vis
    have hcard_vis₁ : vis₁.card = vis.card + 1 := Finset.card_insert_of_notMem hmem
    have hcard_vis₁_le : vis₁.card ≤ N := by
      have := Finset.card_le_univ vis₁; simpa using this
    have hk' : N - vis₁.card ≤ k' := by omega
    have hcons_root : F₀ + 0 + 1 + (N - vis₁.card) ≤ N := by omega
    have hoff_r0 : x.mem (offAddr + r.val) = csrOffset adj r.val := hcsr.1 r.val (by omega)
    have hoff_r1 : x.mem (offAddr + r.val + 1) = csrOffset adj (r.val + 1) := by
      simpa [Nat.add_assoc] using hcsr.1 (r.val + 1) (by omega)
    have hf_or0 : Fits w (offAddr + r.val) := hfit.of_le (by omega)
    have hf_or1 : Fits w (offAddr + r.val + 1) := hfit.of_le (by omega)
    have hf_s1 : Fits w (stkAddr + 1) := hfit.of_le (by omega)
    have hf_s2 : Fits w (stkAddr + 1 + 1) := hfit.of_le (by omega)
    let PushRootPost (x₁ : Data 28) : Prop :=
      DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x₁ ∧
        CSRAt adj offAddr edgeAddr x₁.mem ∧
        VisAt vis₁ visAddr x₁.mem ∧
        x₁.regs pReg = 1 ∧
        x₁.regs finCnt = F₀ ∧
        x₁.mem (stkAddr + 3 * 0) = r.val ∧
        x₁.mem (stkAddr + 3 * 0 + 1) = csrOffset adj r.val + 0 ∧
        x₁.mem (stkAddr + 3 * 0 + 2) = csrOffset adj (r.val + 1) ∧
        (∀ a, ¬ (a = visAddr + r.val ∨ (stkAddr ≤ a ∧ a < stkAddr + 3 * N)) →
          x₁.mem a = x.mem a) ∧
        (∀ reg : Fin 28, (reg.val < 19 ∨ reg = compIdxReg ∨ reg = oldFinReg) →
          x₁.regs reg = x.regs reg)
    have hpush : ∃ x₁, ExecWithin w dfsPushRoot
        ((x.set addr (visAddr + r.val)).set jReg 0) x₁ 11 ∧ PushRootPost x₁ := by
      unfold dfsPushRoot
      wram_exec [hregs.cone, hregs.hoff, hregs.hstk, hu, hoff_r0, hoff_r1,
        hf_or0, hf_or1, hf_s1, hf_s2]
      dsimp only [PushRootPost]
      refine ⟨?_, ?_, ?_, by wram_simp, by wram_simp; exact hfc,
        ?_, ?_, ?_, fun a ha => ?_, fun reg hreg => ?_⟩
      · refine dfsRegs_of_frame hregs fun reg hreg => ?_
        regs_lt
      · mem_upd
        exact hcsr.of_eqOn
          (fun _ _ => by repeat rw [Function.update_of_ne (by omega)])
          (fun _ _ => by repeat rw [Function.update_of_ne (by omega)])
      · intro w_v; mem_upd
        have hw_lt := w_v.isLt
        repeat rw [Function.update_of_ne (by omega)]
        exact visAt_insert hvis r w_v
      · mem_upd
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Nat.add_zero, Function.update_self]
      · mem_upd
        rw [Function.update_of_ne (by omega), Nat.mul_zero, Nat.add_zero, Function.update_self]
        omega
      · mem_upd
        rw [show stkAddr + 2 = stkAddr + 1 + 1 by omega, Function.update_self]
      · mem_upd
        repeat rw [Function.update_of_ne (by omega)]
      · have ha : reg ≠ addr := by reg_ne
        have hj : reg ≠ jReg := by reg_ne
        have hje : reg ≠ jEndReg := by reg_ne
        have hp' : reg ≠ pReg := by reg_ne
        simp only [Data.write_regs_apply, Data.set_regs_of_ne ha, Data.set_regs_of_ne hj,
          Data.set_regs_of_ne hje, Data.set_regs_of_ne hp']
    obtain ⟨x₁, hx₁_ex, hx₁_r, hx₁_csr, hx₁_vis, hx₁_p, hx₁_fc, hx₁_s0, hx₁_s1, hx₁_s2,
      hx₁_out, hx₁_fr⟩ := hpush
    have hs_eq : visit adj N r ⟨vis, []⟩ =
        ⟨(foldEmpty adj k' (adj r) vis₁).visited,
          r :: (foldEmpty adj k' (adj r) vis₁).finished⟩ :=
      (congrArg (fun fuel => visit adj fuel r ⟨vis, []⟩) hkN).trans (visit_eq_foldEmpty hmem)
    obtain ⟨z, ⟨t_loop, ht_loop, he_loop⟩, hRz⟩ := dfsLoop_cps adj offAddr edgeAddr visAddr
      finAddr stkAddr Mc hdisj1 hdisj2 hdisj3 hdisj4 hmc hfit k' r (adj r) 0 0 F₀ 2 vis₁ x₁
      RootPost (by simp) (fun q hq => by simp) hk' hcons_root hx₁_r hx₁_csr hx₁_vis hx₁_p hx₁_fc
      hx₁_s0 hx₁_s1 hx₁_s2
      (fun y hy_r hy_csr hy_vis hy_p hy_fc hy_fin hy_rval hy_out hy_fr => by
        have hend : ¬ (Cond.lt cZero pReg).Holds y := by
          change ¬ y.regs cZero < y.regs pReg
          have := hy_r.czero; omega
        refine ⟨y, ⟨2, le_rfl, Exec.loop_exit hend⟩, ?_⟩
        dsimp only [RootPost]
        rw [hs_eq]
        dsimp only
        refine ⟨hy_r, hy_csr, hy_vis, by rw [List.length_cons, hy_fc]; omega,
          fun q hq => ?_, fun a ha => ?_, fun reg hreg => (hy_fr reg hreg).trans (hx₁_fr reg hreg)⟩
        · simp only [List.reverse_cons, List.length_append, List.length_reverse,
            List.length_singleton] at hq
          by_cases hq_lt : q < (foldEmpty adj k' (adj r) vis₁).finished.length
          · rw [hy_fin q (by simpa using hq_lt)]
            congr 1
            simp only [List.reverse_cons]
            rw [List.getElem_append_left (by simpa using hq_lt)]
          · have hq_eq : q = (foldEmpty adj k' (adj r) vis₁).finished.length := by omega
            subst hq_eq
            rw [hy_rval]
            congr 1
            simp
        · simp only [List.length_cons] at ha
          have h1 := hy_out a (by omega)
          have h0 := hx₁_out a (by omega)
          exact h1.trans h0)
    have hbound : 2 + 1 + 11 + t_loop ≤
        16 + 60 * (visit adj N r ⟨vis, []⟩).finished.length +
          36 * outDegreeSum adj (visit adj N r ⟨vis, []⟩).finished := by
      rw [hs_eq]
      simp only [dfsFrameTime, List.length_cons, outDegreeSum, List.map_cons,
        List.sum_cons] at ht_loop ⊢
      omega
    unfold visitRootCode
    wram_exec [hregs.czero, hregs.hvis, hu, hvis_0, hf_vr]
    refine WP.of_execWithin hx₁_ex ?_
    refine WP.of_execWithin ⟨t_loop, le_rfl, he_loop⟩ ?_
    exact ⟨by omega, hRz⟩


/-! ### Pass 1: Forward DFS finishing order (`O(N + M)`) -/

/-- Visit vertex `iReg` as a DFS root and advance `iReg`. -/
private def forwardDFSBody : Code .standard 28 :=
  (ram[ uReg ← iReg ]).seq (visitRootCode.seq (ram[ iReg ← iReg + cOne ]))

/-- Forward pass: clear the visited flags and visit every vertex as a root, writing the DFS
finishing order at `finB`. -/
def forwardDFSCode : Code .standard 28 :=
  (zeroBlockCode visB).seq
    ((ram[ finCnt ← cZero; iReg ← cZero ]).seq
      (.loop (.lt iReg nVerts) forwardDFSBody))

private theorem forwardDFSLoop_spec {N w : ℕ} (hN : 0 < N) (adj : Fin N → List (Fin N))
    (wb Mc : ℕ) (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (kTopAddr wb N Mc + Mc + 4)) :
    ∀ (rs : List (Fin N)) (idx : ℕ) (vis : Finset (Fin N)) (F₀ : ℕ) (x : Data 28)
      (_ : idx + rs.length = N),
      (∀ q (hq : q < rs.length), rs[q].val = idx + q) →
      F₀ = vis.card →
      DfsRegs (kOffAddr wb) (kEdgeAddr wb N) (kVisAddr wb N Mc) (kOrdAddr wb N Mc)
        (kStkAddr wb N Mc) x →
      CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x.mem →
      VisAt vis (kVisAddr wb N Mc) x.mem →
      x.regs nVerts = N →
      x.regs iReg = idx →
      x.regs finCnt = F₀ →
      ∃ y,
        let s := foldEmpty adj N rs vis
        ExecWithin w (.loop (.lt iReg nVerts) forwardDFSBody) x y
          (22 * rs.length + 60 * s.finished.length + 36 * outDegreeSum adj s.finished + 2) ∧
        DfsRegs (kOffAddr wb) (kEdgeAddr wb N) (kVisAddr wb N Mc) (kOrdAddr wb N Mc)
          (kStkAddr wb N Mc) y ∧
        CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) y.mem ∧
        VisAt s.visited (kVisAddr wb N Mc) y.mem ∧
        y.regs finCnt = F₀ + s.finished.length ∧
        (∀ q (hq : q < s.finished.reverse.length),
          y.mem (kOrdAddr wb N Mc + F₀ + q) = (s.finished.reverse[q]).val) ∧
        (∀ a, ¬ ((kVisAddr wb N Mc ≤ a ∧ a < kVisAddr wb N Mc + N) ∨
            (kOrdAddr wb N Mc + F₀ ≤ a ∧ a < kOrdAddr wb N Mc + F₀ + s.finished.length) ∨
            (kStkAddr wb N Mc ≤ a ∧ a < kStkAddr wb N Mc + 3 * N)) → y.mem a = x.mem a) ∧
        (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r)
  | [], idx, vis, F₀, x, hidx, _, _, hregs, hcsr, hvis, hNv, hi, hfc => by
    simp only [List.length_nil, Nat.add_zero] at hidx
    have hend : ¬ (Cond.lt iReg nVerts).Holds x := by
      change ¬ x.regs iReg < x.regs nVerts; omega
    refine ⟨x, ⟨2, by simp [foldEmpty, outDegreeSum], Exec.loop_exit hend⟩,
      hregs, hcsr, hvis, by simpa [foldEmpty] using hfc,
      fun _ hq => by simp [foldEmpty] at hq, fun _ _ => rfl, fun _ _ => rfl⟩
  | r :: rs, idx, vis, F₀, x, hidx, hrs, hF₀, hregs, hcsr, hvis, hNv, hi, hfc => by
    simp only [List.length_cons] at hidx
    have hr_val : r.val = idx := by
      have h0 := hrs 0 (by simp)
      rwa [List.getElem_cons_zero, Nat.add_zero] at h0
    have hcard_le : vis.card ≤ N := by have := Finset.card_le_univ vis; simpa using this
    have hcons : F₀ + (N - vis.card) ≤ N := by omega
    have hfit_stk : Fits w (kStkAddr wb N Mc + 3 * N + Mc + 4) :=
      hfit.of_le (by simp only [kStkAddr, kTopAddr]; omega)
    let st_u := x.set uReg idx
    obtain ⟨y₁, hy₁_ex, hy₁_r, hy₁_csr, hy₁_vis, hy₁_fc, hy₁_ord, hy₁_out, hy₁_fr⟩ :=
      visitRootCode_spec hN adj (kOffAddr wb) (kEdgeAddr wb N) (kVisAddr wb N Mc)
        (kOrdAddr wb N Mc) (kStkAddr wb N Mc) Mc
        (by simp only [kOffAddr, kVisAddr]; omega)
        (by simp only [kEdgeAddr, kVisAddr]; omega)
        (by simp only [kVisAddr, kOrdAddr]; omega)
        (by simp only [kOrdAddr, kStkAddr]; omega)
        hmc hfit_stk r F₀ vis hcons (x := st_u)
        (dfsRegs_of_frame hregs fun reg hreg => by
          dsimp only [st_u]; regs_lt)
        hcsr hvis (by dsimp only [st_u]; wram_simp; omega)
        (by dsimp only [st_u]; wram_simp; exact hfc)
    set s₁ := visit adj N r ⟨vis, []⟩
    have hy₁_i : y₁.regs iReg = idx :=
      (hy₁_fr iReg (.inl (by decide))).trans (by dsimp only [st_u]; wram_simp; exact hi)
    have hy₁_1 : y₁.regs cOne = 1 := hy₁_r.cone
    have hf_i1 : Fits w (idx + 1) := hfit.of_le (by simp only [kTopAddr]; omega)
    have hbody_ex : ExecWithin w forwardDFSBody x (y₁.set iReg (idx + 1))
        (18 + 60 * s₁.finished.length + 36 * outDegreeSum adj s₁.finished) := by
      have h1 : ExecWithin (B := .standard) w (ram[ uReg ← iReg ]) x st_u 1 := by
        have htriv : st_u = x.set uReg idx := rfl
        wram_exec [hi]
      have h2 : ExecWithin w (ram[ iReg ← iReg + cOne ]) y₁ (y₁.set iReg (idx + 1)) 1 := by
        wram_exec [hy₁_i, hy₁_1, hf_i1]
      exact (h1.seq (hy₁_ex.seq h2)).mono (by omega)
    set x₂ := y₁.set iReg (idx + 1)
    have hcard_s₁ : s₁.visited.card = vis.card + s₁.finished.length :=
      card_visit_nil adj N r vis
    have hcard_s₁_le : s₁.visited.card ≤ N := by
      have := Finset.card_le_univ s₁.visited; simpa using this
    have hrs' : ∀ q (hq : q < rs.length), rs[q].val = (idx + 1) + q := by
      intro q hq
      have h := hrs (q + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 q] using h
    obtain ⟨y, hy_ex, hy_r, hy_csr, hy_vis, hy_fc, hy_ord, hy_out, hy_fr⟩ :=
      forwardDFSLoop_spec hN adj wb Mc hmc hfit rs (idx + 1) s₁.visited
        (F₀ + s₁.finished.length) x₂ (by omega) hrs' (by omega)
        (dfsRegs_of_frame hy₁_r fun reg hreg => by
          dsimp only [x₂]; regs_lt)
        hy₁_csr hy₁_vis
        (by
          dsimp only [x₂]; wram_simp
          exact (hy₁_fr nVerts (.inl (by decide))).trans
            (by dsimp only [st_u]; wram_simp; exact hNv))
        (by dsimp only [x₂]; wram_simp)
        (by dsimp only [x₂]; wram_simp; exact hy₁_fc)
    set s₂ := foldEmpty adj N rs s₁.visited
    have hfold_cons : foldEmpty adj N (r :: rs) vis =
        ⟨s₂.visited, s₂.finished ++ s₁.finished⟩ :=
      foldEmpty_cons adj N r rs vis
    obtain ⟨t₁, ht₁, he₁⟩ := hbody_ex
    obtain ⟨t₂, ht₂, he₂⟩ := hy_ex
    have hlt : (Cond.lt iReg nVerts).Holds x := by
      change x.regs iReg < x.regs nVerts; omega
    refine ⟨y, ⟨t₁ + t₂ + 2, ?_, Exec.loop_iter hlt he₁ he₂⟩, hy_r, hy_csr,
      by simpa [hfold_cons] using hy_vis,
      by rw [hfold_cons]; dsimp only; rw [List.length_append]; omega,
      fun q hq => ?_, fun a ha => ?_, fun reg hreg => ?_⟩
    · rw [hfold_cons]; dsimp only
      rw [List.length_cons, List.length_append, outDegreeSum_append]
      omega
    · have hrev : (foldEmpty adj N (r :: rs) vis).finished.reverse =
          s₁.finished.reverse ++ s₂.finished.reverse := by
        simp [hfold_cons]
      simp only [hrev, List.length_append, List.length_reverse] at hq
      by_cases hq1 : q < s₁.finished.length
      · have hpres : y.mem (kOrdAddr wb N Mc + F₀ + q) = y₁.mem (kOrdAddr wb N Mc + F₀ + q) :=
          hy_out (kOrdAddr wb N Mc + F₀ + q) (by
            dsimp only [kVisAddr, kOrdAddr, kStkAddr] at *; omega)
        rw [hpres, hy₁_ord q (by simpa using hq1)]
        congr 1
        simp only [hrev]
        rw [List.getElem_append_left (by simpa using hq1)]
      · set q' := q - s₁.finished.length
        have hq'_lt : q' < s₂.finished.reverse.length := by simp; omega
        have haddr : kOrdAddr wb N Mc + F₀ + q =
            kOrdAddr wb N Mc + (F₀ + s₁.finished.length) + q' := by omega
        rw [haddr, hy_ord q' hq'_lt]
        congr 1
        simp only [hrev]
        rw [List.getElem_append_right (by simp; omega)]
        simp [q']
    · rw [hfold_cons] at ha; dsimp only at ha; rw [List.length_append] at ha
      have h2 := hy_out a (by dsimp only [kVisAddr, kOrdAddr, kStkAddr] at *; omega)
      have h1 := hy₁_out a (by dsimp only [kVisAddr, kOrdAddr, kStkAddr] at *; omega)
      exact h2.trans h1
    · have h2 := hy_fr reg hreg
      have h1 := hy₁_fr reg (.inl (by omega))
      have hne_i : reg ≠ iReg := by reg_ne
      have hne_u : reg ≠ uReg := by reg_ne
      dsimp only [x₂] at h2
      rw [h2, Data.set_regs_of_ne hne_i, h1]
      dsimp only [st_u]
      exact Data.set_regs_of_ne hne_u _

theorem forwardDFSCode_spec {N w : ℕ} (hN : 0 < N) (adj : Fin N → List (Fin N))
    (wb Mc : ℕ) (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (kTopAddr wb N Mc + Mc + 4)) {x : Data 28}
    (hregs : DfsRegs (kOffAddr wb) (kEdgeAddr wb N) (kVisAddr wb N Mc) (kOrdAddr wb N Mc)
      (kStkAddr wb N Mc) x)
    (hNv : x.regs nVerts = N)
    (hcsr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x.mem) :
    let ord := topologicalSort adj (List.finRange N)
    ∃ y, ExecWithin w forwardDFSCode x y (87 * N + 36 * Mc + 10) ∧
      ord.length = N ∧
      (∀ idx (hidx : idx < N),
        y.mem (kOrdAddr wb N Mc + (N - 1 - idx)) =
          (ord[idx]'(by rw [length_topologicalSort_finRange]; exact hidx)).val) ∧
      CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) y.mem ∧
      (∀ a, ¬ ((kVisAddr wb N Mc ≤ a ∧ a < kVisAddr wb N Mc + N) ∨
          (kOrdAddr wb N Mc ≤ a ∧ a < kOrdAddr wb N Mc + N) ∨
          (kStkAddr wb N Mc ≤ a ∧ a < kStkAddr wb N Mc + 3 * N)) → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r) := by
  have hfit_vis : Fits w (kVisAddr wb N Mc + N) :=
    hfit.of_le (by simp only [kVisAddr, kTopAddr]; omega)
  obtain ⟨x₁, hx₁_ex, hx₁_zero, hx₁_out, hx₁_fr⟩ :=
    zeroBlockCode_spec visB (by decide) (kVisAddr wb N Mc) N hfit_vis hregs.czero hregs.cone
      hregs.hvis hNv
  have hx₁_csr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x₁.mem :=
    hcsr.of_eqOn
      (fun _ _ => hx₁_out _ (by dsimp only [kOffAddr, kVisAddr]; omega))
      (fun _ _ => hx₁_out _ (by dsimp only [kEdgeAddr, kVisAddr]; omega))
  have hx₁_vis : VisAt (∅ : Finset (Fin N)) (kVisAddr wb N Mc) x₁.mem := by
    intro w_v; simp [hx₁_zero w_v.val w_v.isLt]
  have hx₁_r := dfsRegs_of_frame hregs hx₁_fr
  let x₂ := (x₁.set finCnt 0).set iReg 0
  have hprep : ExecWithin (B := .standard) w (ram[ finCnt ← cZero; iReg ← cZero ]) x₁ x₂ 2 := by
    have hc0 := hx₁_r.czero
    wram_exec [hc0]
  obtain ⟨y, hy_ex, -, hy_csr, -, -, hy_ord, hy_out, hy_fr⟩ :=
    forwardDFSLoop_spec hN adj wb Mc hmc hfit (List.finRange N) 0 ∅ 0 x₂ (by simp)
      (fun q hq => by simp) rfl
      (dfsRegs_of_frame hx₁_r fun reg hreg => by
        dsimp only [x₂]; regs_lt)
      hx₁_csr hx₁_vis
      (by dsimp only [x₂]; wram_simp; exact (hx₁_fr nVerts (by decide)).trans hNv)
      (by dsimp only [x₂]; wram_simp)
      (by dsimp only [x₂]; wram_simp)
  set ord := topologicalSort adj (List.finRange N)
  have hfold_eq : (foldEmpty adj N (List.finRange N) ∅).finished = ord := by
    simp [foldEmpty, ord, topologicalSort, dfs]
  have hnd_ord : ord.Nodup := nodup_topologicalSort List.mem_finRange
  have hmem_ord : ∀ v : Fin N, v ∈ ord := mem_topologicalSort List.mem_finRange
  have huniv_ord : ord.toFinset = Finset.univ := by ext v; simp [hmem_ord v]
  have hlen_ord : ord.length = N := length_topologicalSort_finRange adj
  have hout_ord : outDegreeSum adj ord = csrOffset adj N := by
    rw [csrOffset_eq_outDegreeSum]
    unfold outDegreeSum
    rw [← List.sum_toFinset _ hnd_ord, ← List.sum_toFinset _ (List.nodup_finRange N), huniv_ord]
    have huniv2 : (List.finRange N).toFinset = Finset.univ := by ext v; simp
    rw [huniv2]
  rw [hfold_eq] at hy_ex hy_ord hy_out
  rw [hlen_ord, hout_ord] at hy_ex
  simp only [List.length_finRange, Nat.add_zero] at hy_ex hy_ord hy_out
  refine ⟨y, (hx₁_ex.seq (hprep.seq hy_ex)).mono (by omega), hlen_ord,
    fun idx hidx => ?_, hy_csr, fun a ha => ?_, fun r hr => ?_⟩
  · have hrev_idx : N - 1 - idx < ord.reverse.length := by simp [hlen_ord]; omega
    rw [hy_ord (N - 1 - idx) hrev_idx]
    congr 1
    rw [List.getElem_reverse]
    congr 1
    omega
  · rw [hlen_ord] at hy_out
    exact (hy_out a ha).trans (hx₁_out a (by omega))
  · have h2 := hy_fr r hr
    dsimp only [x₂] at h2
    have hne1 : r ≠ iReg := by reg_ne
    have hne2 : r ≠ finCnt := by reg_ne
    rw [h2, Data.set_regs_of_ne hne1, Data.set_regs_of_ne hne2]
    exact hx₁_fr r hr

/-! ### Pass 2: CSR transpose construction (`O(N + M)`) -/

/-- Scan the CSR arcs leaving `uIdxReg` and run `stepBody` on each `(u = uIdxReg, v = vReg)`. -/
private def forEachArcInner (fwdEdgeReg : Fin 28) (stepBody : Code .standard 28) :
    Code .standard 28 :=
  (ram[ addr ← fwdEdgeReg + jReg; vReg ← *addr ]).seq
    (stepBody.seq (ram[ jReg ← jReg + cOne ]))

/-- Scan every CSR vertex `uIdxReg < nVerts` and its outgoing arcs, running `stepBody` on each. -/
private def forEachArc (fwdEdgeReg uIdxReg : Fin 28) (stepBody : Code .standard 28) :
    Code .standard 28 :=
  Code.loop (.lt uIdxReg nVerts)
    ((ram[ addr ← offB + uIdxReg; jReg ← *addr; addr ← addr + cOne; oldFinReg ← *addr ]).seq
      ((Code.loop (.lt jReg oldFinReg) (forEachArcInner fwdEdgeReg stepBody)).seq
        (ram[ uIdxReg ← uIdxReg + cOne ])))

/-- CSR transposition: in-degree count, prefix sums and backward fill of the reversed arcs. -/
def transposeCSRCode : Code .standard 28 :=
  (zeroBlockCode curB).seq
    ((ram[ iReg ← cZero ]).seq
      ((forEachArc edgeB iReg incCurCode).seq
        ((ram[ compIdxReg ← offB; offB ← revOffB ]).seq
          (prefixSumCode.seq
            ((ram[ offB ← compIdxReg; finCnt ← edgeB; edgeB ← revEdgeB; uReg ← cZero ]).seq
              ((forEachArc finCnt uReg backfillStepCode).seq
                (ram[ offB ← revOffB ])))))))

private theorem length_foldl_rev_le {N : ℕ} (u : Fin N) :
    ∀ (es : List (Fin N)) (rev : Fin N → List (Fin N)) (w : Fin N),
      (rev w).length ≤
        (es.foldl (fun r v => Function.update r v (u :: r v)) rev w).length
  | [], _, _ => le_rfl
  | v :: es, rev, w => by
    have h1 : (rev w).length ≤ (Function.update rev v (u :: rev v) w).length := by
      by_cases hw : w = v <;> simp [hw]
    exact h1.trans (length_foldl_rev_le u es (Function.update rev v (u :: rev v)) w)

private theorem length_foldl_vs_rev_le {N : ℕ} (adj : Fin N → List (Fin N)) :
    ∀ (us : List (Fin N)) (rev : Fin N → List (Fin N)) (w : Fin N),
      (rev w).length ≤
        (us.foldl (fun r u => (adj u).foldl (fun r v => Function.update r v (u :: r v)) r)
          rev w).length
  | [], _, _ => le_rfl
  | u :: us, rev, w =>
    (length_foldl_rev_le u (adj u) rev w).trans
      (length_foldl_vs_rev_le adj us _ w)

private abbrev revGraph {N : ℕ} (adj : Fin N → List (Fin N)) : Fin N → List (Fin N) :=
  transposeAdj adj (List.finRange N)

private theorem csrOffset_transposeAdj_eq {N : ℕ} (adj : Fin N → List (Fin N)) :
    csrOffset (transposeAdj adj (List.finRange N)) N = csrOffset adj N := by
  rw [csrOffset_eq_outDegreeSum, csrOffset_eq_outDegreeSum, outDegreeSum, ← Fin.sum_univ_def,
    sum_length_transposeAdj]

private theorem forEachArcInner_spec {N w : ℕ} (adj : Fin N → List (Fin N))
    (wb Mc : ℕ) (hmc : csrOffset adj N ≤ Mc) (hfit : Fits w (kTopAddr wb N Mc + Mc + 4))
    (fwdEdgeReg uIdxReg : Fin 28) (stepBody : Code .standard 28) (stepTime : ℕ)
    (bound : Fin N → ℕ) (Inv : (Fin N → List (Fin N)) → (ℕ → ℕ) → Prop)
    (MemWrite : ℕ → Prop) (ConstRegs : Data 28 → Prop)
    (hu_lo : 18 ≤ uIdxReg.val) (hu_hi : uIdxReg.val < 24)
    (hfwd_hi : fwdEdgeReg.val < 24) (hfwd_ne : fwdEdgeReg ≠ uIdxReg)
    (hdisj : ∀ a, MemWrite a →
      ¬ ((kOffAddr wb ≤ a ∧ a < kOffAddr wb + N + 1) ∨
        (kEdgeAddr wb N ≤ a ∧ a < kEdgeAddr wb N + csrOffset adj N)))
    (hconst_regs : ∀ d₁ d₂ : Data 28,
      (∀ r : Fin 28, r.val < 18 → d₁.regs r = d₂.regs r) → ConstRegs d₁ → ConstRegs d₂)
    (hstep : ∀ (u v : Fin N) (rev : Fin N → List (Fin N)) (s : Data 28),
      (rev v).length + 1 ≤ bound v → Inv rev s.mem →
      s.regs cOne = 1 → s.regs uIdxReg = u.val → s.regs vReg = v.val → ConstRegs s →
      ∃ y, ExecWithin w stepBody s y stepTime ∧
        Inv (Function.update rev v (u :: rev v)) y.mem ∧
        (∀ a, ¬ MemWrite a → y.mem a = s.mem a) ∧
        (∀ r : Fin 28, r ≠ addr → r ≠ jEndReg → y.regs r = s.regs r))
    (u : Fin N) :
    ∀ (es : List (Fin N)) (k : ℕ) (rev : Fin N → List (Fin N)) (x : Data 28)
      (_ : k + es.length = (adj u).length),
      (∀ q (hq : q < es.length), (adj u)[k + q]'(by omega) = es[q]) →
      (∀ z : Fin N,
        (es.foldl (fun r v => Function.update r v (u :: r v)) rev z).length ≤ bound z) →
      Inv rev x.mem → CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x.mem →
      x.regs cOne = 1 → x.regs fwdEdgeReg = kEdgeAddr wb N → ConstRegs x →
      x.regs uIdxReg = u.val → x.regs jReg = csrOffset adj u.val + k →
      x.regs oldFinReg = csrOffset adj u.val + (adj u).length →
      ∃ y, ExecWithin w (.loop (.lt jReg oldFinReg) (forEachArcInner fwdEdgeReg stepBody)) x y
          ((stepTime + 5) * es.length + 2) ∧
        Inv (es.foldl (fun r v => Function.update r v (u :: r v)) rev) y.mem ∧
        (∀ a, ¬ MemWrite a → y.mem a = x.mem a) ∧
        (∀ r : Fin 28, r ≠ addr → r ≠ jEndReg → r ≠ vReg → r ≠ jReg → y.regs r = x.regs r)
  | [], k, rev, x, hk, _, _, hinv, _, _, _, _, _, hj, hof => by
    simp only [List.length_nil, Nat.add_zero] at hk
    have hend : ¬ (Cond.lt jReg oldFinReg).Holds x := by
      change ¬ x.regs jReg < x.regs oldFinReg; omega
    exact ⟨x, ⟨2, by simp, Exec.loop_exit hend⟩, hinv, fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  | v :: es, k, rev, x, hk, hget, hroom_all, hinv, hcsr, hc1, hfwd, hconst, huR, hj, hof => by
    simp only [List.length_cons] at hk
    have hk_lt : k < (adj u).length := by omega
    have hv_eq : (adj u)[k] = v := by
      have h0 := hget 0 (by simp)
      simpa only [Nat.add_zero, List.getElem_cons_zero] using h0
    have hmem_e : x.mem (kEdgeAddr wb N + (csrOffset adj u.val + k)) = v.val := by
      rw [← Nat.add_assoc, hcsr.2 u k hk_lt, hv_eq]
    have hj_lt_M : csrOffset adj u.val + k < csrOffset adj N := by
      have h1 := csrOffset_succ adj u.isLt; simp only [Fin.eta] at h1
      have h2 := csrOffset_mono adj (by omega : u.val + 1 ≤ N); omega
    have hf_eaddr : Fits w (kEdgeAddr wb N + (csrOffset adj u.val + k)) :=
      hfit.of_le (by simp only [kEdgeAddr, kTopAddr]; omega)
    have hf_j1 : Fits w (csrOffset adj u.val + k + 1) :=
      hfit.of_le (by simp only [kTopAddr]; omega)
    have hroom_v : (rev v).length + 1 ≤ bound v := by
      have hle := length_foldl_rev_le u es (Function.update rev v (u :: rev v)) v
      have hall := hroom_all v
      simp only [List.foldl_cons] at hall
      simpa using hle.trans hall
    let st_v := (x.set addr (kEdgeAddr wb N + (csrOffset adj u.val + k))).set vReg v.val
    have hst_fr : ∀ r : Fin 28, r.val < 18 → st_v.regs r = x.regs r := fun r hr => by
      dsimp only [st_v]; rw [Data.set_regs_of_ne (by reg_ne), Data.set_regs_of_ne (by reg_ne)]
    have hst_u : st_v.regs uIdxReg = u.val := by
      dsimp only [st_v]
      have h1 : uIdxReg ≠ vReg := Fin.ne_of_val_ne (by change uIdxReg.val ≠ 24; omega)
      have h2 : uIdxReg ≠ addr := Fin.ne_of_val_ne (by change uIdxReg.val ≠ 27; omega)
      rw [Data.set_regs_of_ne h1, Data.set_regs_of_ne h2, huR]
    have hst_c1 : st_v.regs cOne = 1 := (hst_fr cOne (by decide)).trans hc1
    obtain ⟨y₁, hy₁_ex, hy₁_inv, hy₁_out, hy₁_fr⟩ :=
      hstep u v rev st_v hroom_v hinv hst_c1 hst_u
        (by dsimp only [st_v]; wram_simp) (hconst_regs _ _ (fun r hr => (hst_fr r hr).symm) hconst)
    have hp1 : ExecWithin (B := .standard) w (ram[ addr ← fwdEdgeReg + jReg; vReg ← *addr ])
        x st_v 2 := by
      have hfwd_ne_a : fwdEdgeReg ≠ addr := Fin.ne_of_val_ne (by change fwdEdgeReg.val ≠ 27; omega)
      have hj_ne_a : jReg ≠ addr := by reg_ne
      have h1 : Exec (B := .standard) w (ram[ addr ← fwdEdgeReg + jReg ]) x
          (x.set addr (kEdgeAddr wb N + (csrOffset adj u.val + k))) 1 := by
        have h : Exec (B := .standard) w (ram[ addr ← fwdEdgeReg + jReg ]) x _ 1 :=
          Exec.bin (by
            change Fits w (x.regs fwdEdgeReg + x.regs jReg); rw [hfwd, hj]; exact hf_eaddr)
        simpa [BinOp.eval, hfwd, hj] using h
      have h2 : Exec (B := .standard) w (ram[ vReg ← *addr ])
          (x.set addr (kEdgeAddr wb N + (csrOffset adj u.val + k))) st_v 1 := by
        have h := Exec.load (B := .standard) (w := w)
          (x := x.set addr (kEdgeAddr wb N + (csrOffset adj u.val + k))) (d := vReg) (a := addr)
        simpa [Data.set_regs_self, Data.set_mem, hmem_e, st_v] using h
      exact ⟨2, le_rfl, h1.seq h2⟩
    have hy₁_1 : y₁.regs cOne = 1 :=
      (hy₁_fr cOne (by decide) (by decide)).trans hst_c1
    have hy₁_j : y₁.regs jReg = csrOffset adj u.val + k :=
      (hy₁_fr jReg (by decide) (by decide)).trans (by dsimp only [st_v]; wram_simp; exact hj)
    let x₂ := y₁.set jReg (csrOffset adj u.val + (k + 1))
    have hp2 : ExecWithin w (ram[ jReg ← jReg + cOne ]) y₁ x₂ 1 := by
      have htriv : x₂ = y₁.set jReg (csrOffset adj u.val + k + 1) := by
        simp [x₂, Nat.add_assoc]
      rw [htriv]
      wram_exec [hy₁_j, hy₁_1, hf_j1]
    have hx₂_csr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x₂.mem :=
      hcsr.of_eqOn
        (fun i hi => by
          by_contra hne
          have hmem : MemWrite (kOffAddr wb + i) := by
            by_contra hnw; exact hne (hy₁_out _ hnw)
          exact hdisj _ hmem (.inl ⟨by omega, by omega⟩))
        (fun e he => by
          by_contra hne
          have hmem : MemWrite (kEdgeAddr wb N + e) := by
            by_contra hnw; exact hne (hy₁_out _ hnw)
          exact hdisj _ hmem (.inr ⟨by omega, by omega⟩))
    have hx₂_fr : ∀ r : Fin 28, r.val < 18 → x₂.regs r = x.regs r := fun r hr => by
      dsimp only [x₂]
      rw [Data.set_regs_of_ne (by reg_ne), hy₁_fr r (by reg_ne) (by reg_ne), hst_fr r hr]
    have hx₂_fwd : x₂.regs fwdEdgeReg = kEdgeAddr wb N := by
      dsimp only [x₂]
      have h1 : fwdEdgeReg ≠ jReg := Fin.ne_of_val_ne (by change fwdEdgeReg.val ≠ 25; omega)
      have h2 : fwdEdgeReg ≠ addr := Fin.ne_of_val_ne (by change fwdEdgeReg.val ≠ 27; omega)
      have h3 : fwdEdgeReg ≠ jEndReg := Fin.ne_of_val_ne (by change fwdEdgeReg.val ≠ 26; omega)
      have h4 : fwdEdgeReg ≠ vReg := Fin.ne_of_val_ne (by change fwdEdgeReg.val ≠ 24; omega)
      rw [Data.set_regs_of_ne h1, hy₁_fr fwdEdgeReg h2 h3]
      dsimp only [st_v]
      rw [Data.set_regs_of_ne h4, Data.set_regs_of_ne h2, hfwd]
    have hx₂_u : x₂.regs uIdxReg = u.val := by
      dsimp only [x₂]
      have h1 : uIdxReg ≠ jReg := Fin.ne_of_val_ne (by change uIdxReg.val ≠ 25; omega)
      have h2 : uIdxReg ≠ addr := Fin.ne_of_val_ne (by change uIdxReg.val ≠ 27; omega)
      have h3 : uIdxReg ≠ jEndReg := Fin.ne_of_val_ne (by change uIdxReg.val ≠ 26; omega)
      rw [Data.set_regs_of_ne h1, hy₁_fr uIdxReg h2 h3, hst_u]
    have hx₂_of : x₂.regs oldFinReg = csrOffset adj u.val + (adj u).length := by
      dsimp only [x₂]
      rw [Data.set_regs_of_ne (by reg_ne), hy₁_fr oldFinReg (by decide) (by decide)]
      dsimp only [st_v]; wram_simp; exact hof
    obtain ⟨y, hy_ex, hy_inv, hy_out, hy_fr⟩ :=
      forEachArcInner_spec adj wb Mc hmc hfit fwdEdgeReg uIdxReg stepBody stepTime bound Inv
        MemWrite ConstRegs hu_lo hu_hi hfwd_hi hfwd_ne hdisj hconst_regs hstep u es (k + 1)
        (Function.update rev v (u :: rev v)) x₂ (by omega)
        (fun q hq => by
          have h := hget (q + 1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 q] using h)
        (fun z => by simpa [List.foldl_cons] using hroom_all z)
        hy₁_inv hx₂_csr ((hx₂_fr cOne (by decide)).trans hc1) hx₂_fwd
        (hconst_regs _ _ (fun r hr => (hx₂_fr r hr).symm) hconst) hx₂_u
        (by dsimp only [x₂]; wram_simp) hx₂_of
    have hbody_ex : ExecWithin w (forEachArcInner fwdEdgeReg stepBody) x x₂ (stepTime + 3) :=
      (hp1.seq (hy₁_ex.seq hp2)).mono (by omega)
    obtain ⟨t₁, ht₁, he₁⟩ := hbody_ex
    obtain ⟨t₂, ht₂, he₂⟩ := hy_ex
    have hlt : (Cond.lt jReg oldFinReg).Holds x := by
      change x.regs jReg < x.regs oldFinReg; omega
    refine ⟨y, ⟨t₁ + t₂ + 2, by simp only [List.length_cons]; rw [Nat.mul_add, Nat.mul_one]; omega,
        Exec.loop_iter hlt he₁ he₂⟩,
      hy_inv, fun a ha => (hy_out a ha).trans (hy₁_out a ha), fun r h1 h2 h3 h4 => ?_⟩
    rw [hy_fr r h1 h2 h3 h4]
    dsimp only [x₂]
    rw [Data.set_regs_of_ne h4, hy₁_fr r h1 h2]
    dsimp only [st_v]
    rw [Data.set_regs_of_ne h3, Data.set_regs_of_ne h1]

private theorem forEachArc_spec {N w : ℕ} (adj : Fin N → List (Fin N))
    (wb Mc : ℕ) (hmc : csrOffset adj N ≤ Mc) (hfit : Fits w (kTopAddr wb N Mc + Mc + 4))
    (fwdEdgeReg uIdxReg : Fin 28) (stepBody : Code .standard 28) (stepTime : ℕ)
    (bound : Fin N → ℕ) (Inv : (Fin N → List (Fin N)) → (ℕ → ℕ) → Prop)
    (MemWrite : ℕ → Prop) (ConstRegs : Data 28 → Prop)
    (hu_lo : 18 ≤ uIdxReg.val) (hu_hi : uIdxReg.val < 24) (hu_ne_of : uIdxReg ≠ oldFinReg)
    (hfwd_hi : fwdEdgeReg.val < 24) (hfwd_ne_of : fwdEdgeReg ≠ oldFinReg)
    (hfwd_ne : fwdEdgeReg ≠ uIdxReg)
    (hdisj : ∀ a, MemWrite a →
      ¬ ((kOffAddr wb ≤ a ∧ a < kOffAddr wb + N + 1) ∨
        (kEdgeAddr wb N ≤ a ∧ a < kEdgeAddr wb N + csrOffset adj N)))
    (hconst_regs : ∀ d₁ d₂ : Data 28,
      (∀ r : Fin 28, r.val < 18 → d₁.regs r = d₂.regs r) → ConstRegs d₁ → ConstRegs d₂)
    (hstep : ∀ (u v : Fin N) (rev : Fin N → List (Fin N)) (s : Data 28),
      (rev v).length + 1 ≤ bound v → Inv rev s.mem →
      s.regs cOne = 1 → s.regs uIdxReg = u.val → s.regs vReg = v.val → ConstRegs s →
      ∃ y, ExecWithin w stepBody s y stepTime ∧
        Inv (Function.update rev v (u :: rev v)) y.mem ∧
        (∀ a, ¬ MemWrite a → y.mem a = s.mem a) ∧
        (∀ r : Fin 28, r ≠ addr → r ≠ jEndReg → y.regs r = s.regs r)) :
    ∀ (us : List (Fin N)) (idx : ℕ) (rev : Fin N → List (Fin N)) (x : Data 28)
      (_ : idx + us.length = N),
      (∀ q (hq : q < us.length), us[q].val = idx + q) →
      (∀ z : Fin N,
        (us.foldl (fun r u => (adj u).foldl (fun r v => Function.update r v (u :: r v)) r)
          rev z).length ≤ bound z) →
      Inv rev x.mem → CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x.mem →
      x.regs cOne = 1 → x.regs nVerts = N → x.regs offB = kOffAddr wb →
      x.regs fwdEdgeReg = kEdgeAddr wb N → ConstRegs x → x.regs uIdxReg = idx →
      ∃ y, ExecWithin w (forEachArc fwdEdgeReg uIdxReg stepBody) x y
          (9 * us.length + (stepTime + 5) * outDegreeSum adj us + 2) ∧
        Inv (us.foldl (fun r u => (adj u).foldl (fun r v => Function.update r v (u :: r v)) r)
          rev) y.mem ∧
        (∀ a, ¬ MemWrite a → y.mem a = x.mem a) ∧
        (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r)
  | [], idx, rev, x, hidx, _, _, hinv, _, _, hNv, _, _, _, huIdx => by
    simp only [List.length_nil, Nat.add_zero] at hidx
    have hend : ¬ (Cond.lt uIdxReg nVerts).Holds x := by
      change ¬ x.regs uIdxReg < x.regs nVerts; omega
    exact ⟨x, ⟨2, by simp [outDegreeSum], Exec.loop_exit hend⟩,
      hinv, fun _ _ => rfl, fun _ _ => rfl⟩
  | u :: us, idx, rev, x, hidx, hus, hroom_all, hinv, hcsr, hc1, hNv, hoff, hfwd, hconst,
      huIdx => by
    simp only [List.length_cons] at hidx
    have hu_val : u.val = idx := by
      have h0 := hus 0 (by simp)
      rwa [List.getElem_cons_zero, Nat.add_zero] at h0
    have hoff_u : x.mem (kOffAddr wb + idx) = csrOffset adj u.val := by
      rw [← hu_val]; exact hcsr.1 u.val (by omega)
    have hoff_u1 : x.mem (kOffAddr wb + idx + 1) = csrOffset adj u.val + (adj u).length := by
      simpa [← hu_val, Nat.add_assoc, csrOffset_succ adj u.isLt] using
        hcsr.1 (u.val + 1) (by omega)
    have hf_oa : Fits w (kOffAddr wb + idx) :=
      hfit.of_le (by simp only [kOffAddr, kTopAddr]; omega)
    have hf_oa1 : Fits w (kOffAddr wb + idx + 1) :=
      hfit.of_le (by simp only [kOffAddr, kTopAddr]; omega)
    have hf_i1 : Fits w (idx + 1) := hfit.of_le (by simp only [kTopAddr]; omega)
    let x₁ := (((x.set addr (kOffAddr wb + idx)).set jReg (csrOffset adj u.val)).set
      addr (kOffAddr wb + idx + 1)).set oldFinReg (csrOffset adj u.val + (adj u).length)
    have hp1 : ExecWithin (B := .standard) w
        (ram[ addr ← offB + uIdxReg; jReg ← *addr; addr ← addr + cOne; oldFinReg ← *addr ])
        x x₁ 4 := by
      let d₁ := x.set addr (kOffAddr wb + idx)
      let d₂ := d₁.set jReg (csrOffset adj u.val)
      let d₃ := d₂.set addr (kOffAddr wb + idx + 1)
      have h_u1 : uIdxReg ≠ addr := Fin.ne_of_val_ne (by change uIdxReg.val ≠ 27; omega)
      have he1 : Exec (B := .standard) w (ram[ addr ← offB + uIdxReg ]) x d₁ 1 := by
        have h : Exec (B := .standard) w (ram[ addr ← offB + uIdxReg ]) x _ 1 :=
          Exec.bin (by change Fits w (x.regs offB + x.regs uIdxReg); rw [hoff, huIdx]; exact hf_oa)
        simpa [d₁, BinOp.eval, hoff, huIdx] using h
      have he2 : Exec (B := .standard) w (ram[ jReg ← *addr ]) d₁ d₂ 1 := by
        have h := Exec.load (B := .standard) (w := w) (x := d₁) (d := jReg) (a := addr)
        simpa [d₂, d₁, Data.set_regs_self, Data.set_mem, hoff_u] using h
      have he3 : Exec (B := .standard) w (ram[ addr ← addr + cOne ]) d₂ d₃ 1 := by
        have hc1_2 : d₂.regs cOne = 1 := by
          dsimp only [d₂, d₁]
          rw [Data.set_regs_of_ne (by reg_ne), Data.set_regs_of_ne (by reg_ne), hc1]
        have ha_2 : d₂.regs addr = kOffAddr wb + idx := by
          dsimp only [d₂, d₁]; rw [Data.set_regs_of_ne (by reg_ne), Data.set_regs_self]
        have h : Exec (B := .standard) w (ram[ addr ← addr + cOne ]) d₂ _ 1 :=
          Exec.bin (by change Fits w (d₂.regs addr + d₂.regs cOne); rw [ha_2, hc1_2]; exact hf_oa1)
        simpa [d₃, BinOp.eval, ha_2, show d₂.regs 1 = 1 from hc1_2] using h
      have he4 : Exec (B := .standard) w (ram[ oldFinReg ← *addr ]) d₃ x₁ 1 := by
        have h := Exec.load (B := .standard) (w := w) (x := d₃) (d := oldFinReg) (a := addr)
        simpa [x₁, d₃, d₂, d₁, Data.set_regs_self, Data.set_mem, hoff_u1] using h
      exact ⟨4, le_rfl, he1.seq (he2.seq (he3.seq he4))⟩
    have hx₁_fr : ∀ r : Fin 28, r.val < 18 → x₁.regs r = x.regs r := fun r hr => by
      dsimp only [x₁]
      simp [Data.set_regs_of_ne (by reg_ne : r ≠ oldFinReg),
        Data.set_regs_of_ne (by reg_ne : r ≠ addr), Data.set_regs_of_ne (by reg_ne : r ≠ jReg)]
    have hx₁_fwd : x₁.regs fwdEdgeReg = kEdgeAddr wb N := by
      dsimp only [x₁]
      have h2 : fwdEdgeReg ≠ addr := Fin.ne_of_val_ne (by change fwdEdgeReg.val ≠ 27; omega)
      have h3 : fwdEdgeReg ≠ jReg := Fin.ne_of_val_ne (by change fwdEdgeReg.val ≠ 25; omega)
      rw [Data.set_regs_of_ne hfwd_ne_of, Data.set_regs_of_ne h2, Data.set_regs_of_ne h3,
        Data.set_regs_of_ne h2, hfwd]
    have hx₁_u : x₁.regs uIdxReg = u.val := by
      dsimp only [x₁]
      have h2 : uIdxReg ≠ addr := Fin.ne_of_val_ne (by change uIdxReg.val ≠ 27; omega)
      have h3 : uIdxReg ≠ jReg := Fin.ne_of_val_ne (by change uIdxReg.val ≠ 25; omega)
      rw [Data.set_regs_of_ne hu_ne_of, Data.set_regs_of_ne h2, Data.set_regs_of_ne h3,
        Data.set_regs_of_ne h2, huIdx, hu_val]
    have hroom_u : ∀ z : Fin N,
        ((adj u).foldl (fun r v => Function.update r v (u :: r v)) rev z).length ≤ bound z := by
      intro z
      have hle : ((adj u).foldl (fun r v => Function.update r v (u :: r v)) rev z).length ≤
          (us.foldl (fun r u' => (adj u').foldl (fun r v => Function.update r v (u' :: r v)) r)
            ((adj u).foldl (fun r v => Function.update r v (u :: r v)) rev) z).length :=
        length_foldl_vs_rev_le adj us _ z
      exact hle.trans (by simpa [List.foldl_cons] using hroom_all z)
    obtain ⟨y₁, hy₁_ex, hy₁_inv, hy₁_out, hy₁_fr⟩ :=
      forEachArcInner_spec adj wb Mc hmc hfit fwdEdgeReg uIdxReg stepBody stepTime bound Inv
        MemWrite ConstRegs hu_lo hu_hi hfwd_hi hfwd_ne hdisj hconst_regs hstep u (adj u) 0 rev x₁
        (by simp) (fun q _ => by simp) hroom_u (by dsimp only [x₁]; exact hinv)
        (by dsimp only [x₁]; exact hcsr)
        ((hx₁_fr cOne (by decide)).trans hc1) hx₁_fwd
        (hconst_regs _ _ (fun r hr => (hx₁_fr r hr).symm) hconst) hx₁_u
        (by dsimp only [x₁]; wram_simp) (by dsimp only [x₁]; wram_simp)
    have hy₁_u : y₁.regs uIdxReg = idx := by
      have h1 : uIdxReg ≠ addr := Fin.ne_of_val_ne (by change uIdxReg.val ≠ 27; omega)
      have h2 : uIdxReg ≠ jEndReg := Fin.ne_of_val_ne (by change uIdxReg.val ≠ 26; omega)
      have h3 : uIdxReg ≠ vReg := Fin.ne_of_val_ne (by change uIdxReg.val ≠ 24; omega)
      have h4 : uIdxReg ≠ jReg := Fin.ne_of_val_ne (by change uIdxReg.val ≠ 25; omega)
      rw [hy₁_fr uIdxReg h1 h2 h3 h4, hx₁_u, hu_val]
    have hy₁_1 : y₁.regs cOne = 1 :=
      (hy₁_fr cOne (by decide) (by decide) (by decide) (by decide)).trans
        ((hx₁_fr cOne (by decide)).trans hc1)
    let x₂ := y₁.set uIdxReg (idx + 1)
    have hp2 : ExecWithin (B := .standard) w (ram[ uIdxReg ← uIdxReg + cOne ]) y₁ x₂ 1 := by
      have h : Exec (B := .standard) w (ram[ uIdxReg ← uIdxReg + cOne ]) y₁ _ 1 :=
        Exec.bin (by change Fits w (y₁.regs uIdxReg + y₁.regs cOne); rw [hy₁_u, hy₁_1]; exact hf_i1)
      exact ⟨1, le_rfl, by simpa [x₂, BinOp.eval, hy₁_u, show y₁.regs 1 = 1 from hy₁_1] using h⟩
    have hx₂_csr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x₂.mem :=
      hcsr.of_eqOn
        (fun i hi => by
          by_contra hne
          have hmem : MemWrite (kOffAddr wb + i) := by
            by_contra hnw; exact hne (hy₁_out _ hnw)
          exact hdisj _ hmem (.inl ⟨by omega, by omega⟩))
        (fun e he => by
          by_contra hne
          have hmem : MemWrite (kEdgeAddr wb N + e) := by
            by_contra hnw; exact hne (hy₁_out _ hnw)
          exact hdisj _ hmem (.inr ⟨by omega, by omega⟩))
    have hx₂_fr0 : ∀ r : Fin 28, r.val < 18 → x₂.regs r = x.regs r := fun r hr => by
      have hne_u : r ≠ uIdxReg := Fin.ne_of_val_ne (by omega)
      dsimp only [x₂]
      rw [Data.set_regs_of_ne hne_u, hy₁_fr r (by reg_ne) (by reg_ne) (by reg_ne) (by reg_ne),
        hx₁_fr r hr]
    have hx₂_fwd : x₂.regs fwdEdgeReg = kEdgeAddr wb N := by
      have h1 : fwdEdgeReg ≠ addr := Fin.ne_of_val_ne (by change fwdEdgeReg.val ≠ 27; omega)
      have h2 : fwdEdgeReg ≠ jEndReg := Fin.ne_of_val_ne (by change fwdEdgeReg.val ≠ 26; omega)
      have h3 : fwdEdgeReg ≠ vReg := Fin.ne_of_val_ne (by change fwdEdgeReg.val ≠ 24; omega)
      have h4 : fwdEdgeReg ≠ jReg := Fin.ne_of_val_ne (by change fwdEdgeReg.val ≠ 25; omega)
      dsimp only [x₂]
      rw [Data.set_regs_of_ne hfwd_ne, hy₁_fr fwdEdgeReg h1 h2 h3 h4, hx₁_fwd]
    obtain ⟨y, hy_ex, hy_inv, hy_out, hy_fr⟩ :=
      forEachArc_spec adj wb Mc hmc hfit fwdEdgeReg uIdxReg stepBody stepTime bound Inv MemWrite
        ConstRegs hu_lo hu_hi hu_ne_of hfwd_hi hfwd_ne_of hfwd_ne hdisj hconst_regs hstep
        us (idx + 1) ((adj u).foldl (fun r v => Function.update r v (u :: r v)) rev) x₂ (by omega)
        (fun q hq => by
          have h := hus (q + 1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 q] using h)
        (fun z => by simpa [List.foldl_cons] using hroom_all z)
        hy₁_inv hx₂_csr ((hx₂_fr0 cOne (by decide)).trans hc1)
        ((hx₂_fr0 nVerts (by decide)).trans hNv) ((hx₂_fr0 offB (by decide)).trans hoff)
        hx₂_fwd (hconst_regs _ _ (fun r hr => (hx₂_fr0 r hr).symm) hconst)
        (by dsimp only [x₂]; wram_simp)
    have hbody_ex : ExecWithin w
        ((ram[ addr ← offB + uIdxReg; jReg ← *addr; addr ← addr + cOne; oldFinReg ← *addr ]).seq
          ((Code.loop (.lt jReg oldFinReg) (forEachArcInner fwdEdgeReg stepBody)).seq
            (ram[ uIdxReg ← uIdxReg + cOne ])))
        x x₂ (9 + (stepTime + 5) * (adj u).length - 2) := by
      have := (hp1.seq (hy₁_ex.seq hp2)).mono
        (show 4 + ((stepTime + 5) * (adj u).length + 2 + 1) ≤
          9 + (stepTime + 5) * (adj u).length - 2 by omega)
      exact this
    obtain ⟨t₁, ht₁, he₁⟩ := hbody_ex
    obtain ⟨t₂, ht₂, he₂⟩ := hy_ex
    have hlt : (Cond.lt uIdxReg nVerts).Holds x := by
      change x.regs uIdxReg < x.regs nVerts; omega
    refine ⟨y, ⟨t₁ + t₂ + 2, ?_, Exec.loop_iter hlt he₁ he₂⟩,
      hy_inv, fun a ha => (hy_out a ha).trans (hy₁_out a ha),
      fun r hr => (hy_fr r hr).trans (hx₂_fr0 r hr)⟩
    simp only [List.length_cons, outDegreeSum, List.map_cons, List.sum_cons,
      Nat.mul_add, Nat.mul_one] at ht₂ ⊢
    omega

theorem transposeCSRCode_spec {N w : ℕ} (adj : Fin N → List (Fin N))
    (wb Mc : ℕ) (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (kTopAddr wb N Mc + Mc + 4)) {x : Data 28}
    (hc0 : x.regs cZero = 0) (hc1 : x.regs cOne = 1) (hNv : x.regs nVerts = N)
    (hoff : x.regs offB = kOffAddr wb) (hedge : x.regs edgeB = kEdgeAddr wb N)
    (hcur : x.regs curB = kCurAddr wb N Mc)
    (hroff : x.regs revOffB = kRevOffAddr wb N Mc)
    (hredge : x.regs revEdgeB = kRevEdgeAddr wb N Mc)
    (hcsr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x.mem) :
    let revAdj := transposeAdj adj (List.finRange N)
    ∃ y, ExecWithin w transposeCSRCode x y (31 * N + 20 * Mc + 22) ∧
      CSRAt revAdj (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc) y.mem ∧
      y.regs offB = kRevOffAddr wb N Mc ∧
      y.regs edgeB = kRevEdgeAddr wb N Mc ∧
      (∀ a, ¬ ((kRevOffAddr wb N Mc ≤ a ∧ a < kRevOffAddr wb N Mc + N + 1) ∨
          (kRevEdgeAddr wb N Mc ≤ a ∧ a < kRevEdgeAddr wb N Mc + Mc) ∨
          (kCurAddr wb N Mc ≤ a ∧ a < kCurAddr wb N Mc + N)) → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r.val < 18 → r ≠ offB → r ≠ edgeB → y.regs r = x.regs r) := by
  set revAdj := transposeAdj adj (List.finRange N)
  have hmc_rev : csrOffset revAdj N ≤ Mc := by
    dsimp only [revAdj]; rwa [csrOffset_transposeAdj_eq]
  have hfit_cur : Fits w (kCurAddr wb N Mc + N) :=
    hfit.of_le (by simp only [kCurAddr, kTopAddr]; omega)
  obtain ⟨x₁, hx₁_ex, hx₁_zero, hx₁_out, hx₁_fr⟩ :=
    zeroBlockCode_spec curB (by decide) (kCurAddr wb N Mc) N hfit_cur hc0 hc1 hcur hNv
  have hx₁_csr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x₁.mem :=
    hcsr.of_eqOn
      (fun _ _ => hx₁_out _ (by dsimp only [kOffAddr, kCurAddr]; omega))
      (fun _ _ => hx₁_out _ (by dsimp only [kEdgeAddr, kCurAddr]; omega))
  let x₂ := x₁.set iReg 0
  have hp1 : ExecWithin (B := .standard) w (ram[ iReg ← cZero ]) x₁ x₂ 1 := by
    have h0' : x₁.regs cZero = 0 := (hx₁_fr cZero (by decide)).trans hc0
    wram_exec [h0']
  have hroom_rev : ∀ z : Fin N, (revAdj z).length ≤ Mc := by
    intro z
    have h1 := csrOffset_succ revAdj z.isLt; simp only [Fin.eta] at h1
    have h2 := csrOffset_mono revAdj (by omega : z.val + 1 ≤ N); omega
  have hf_cur : Fits w (kCurAddr wb N Mc + N + Mc + 1) :=
    hfit.of_le (by simp only [kCurAddr, kTopAddr]; omega)
  obtain ⟨x₃, hx₃_ex, hx₃_deg, hx₃_out, hx₃_fr⟩ :=
    forEachArc_spec adj wb Mc hmc hfit edgeB iReg incCurCode 4 (fun _ => Mc)
      (fun rev mem => ∀ z : Fin N, mem (kCurAddr wb N Mc + z.val) = (rev z).length)
      (fun a => kCurAddr wb N Mc ≤ a ∧ a < kCurAddr wb N Mc + N)
      (fun d => d.regs curB = kCurAddr wb N Mc)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun a ha => by dsimp only [kOffAddr, kEdgeAddr, kCurAddr] at ha ⊢; omega)
      (fun d₁ d₂ hd h => by rw [← hd curB (by decide)]; exact h)
      (fun u v rev s hroom hinv hc1' _ hv hcur' => by
        obtain ⟨y, hy_ex, hy_deg, hy_out, hy_fr⟩ :=
          incCurCode_spec (kCurAddr wb N Mc) Mc hf_cur (fun z => (rev z).length) v hroom
            hc1' hcur' hv hinv
        refine ⟨y, hy_ex, fun z => ?_, hy_out, hy_fr⟩
        rw [hy_deg z]
        by_cases hz : z = v <;> simp [hz])
      (List.finRange N) 0 (fun _ => []) x₂ (by simp) (fun q _ => by simp)
      (fun z => hroom_rev z) (fun z => by dsimp only [x₂]; exact hx₁_zero z.val z.isLt)
      hx₁_csr (by dsimp only [x₂]; wram_simp; exact (hx₁_fr cOne (by decide)).trans hc1)
      (by dsimp only [x₂]; wram_simp; exact (hx₁_fr nVerts (by decide)).trans hNv)
      (by dsimp only [x₂]; wram_simp; exact (hx₁_fr offB (by decide)).trans hoff)
      (by dsimp only [x₂]; wram_simp; exact (hx₁_fr edgeB (by decide)).trans hedge)
      (by dsimp only [x₂]; wram_simp; exact (hx₁_fr curB (by decide)).trans hcur)
      (by dsimp only [x₂]; wram_simp)
  have hx₃_fr0 : ∀ r : Fin 28, r.val < 18 → x₃.regs r = x.regs r := fun r hr => by
    have h3 := hx₃_fr r hr
    have hne : r ≠ iReg := by reg_ne
    dsimp only [x₂] at h3
    rw [h3, Data.set_regs_of_ne hne]
    exact hx₁_fr r hr
  let x₄ := (x₃.set compIdxReg (kOffAddr wb)).set offB (kRevOffAddr wb N Mc)
  have hp2 : ExecWithin (B := .standard) w (ram[ compIdxReg ← offB; offB ← revOffB ]) x₃ x₄ 2 := by
    have h_ob : x₃.regs offB = kOffAddr wb := (hx₃_fr0 offB (by decide)).trans hoff
    have h_rob : x₃.regs revOffB = kRevOffAddr wb N Mc := (hx₃_fr0 revOffB (by decide)).trans hroff
    wram_exec [h_ob, h_rob]
  have hfit_ps : Fits w (kCurAddr wb N Mc + N + Mc + 2) :=
    hfit.of_le (by simp only [kCurAddr, kTopAddr]; omega)
  obtain ⟨x₅, hx₅_ex, hx₅_roff, hx₅_cur, hx₅_out, hx₅_fr⟩ :=
    prefixSumCode_spec revAdj (kCurAddr wb N Mc) (kRevOffAddr wb N Mc) Mc
      (by simp only [kRevOffAddr, kCurAddr]; omega) hmc_rev hfit_ps (x := x₄)
      (by dsimp only [x₄]; wram_simp; exact (hx₃_fr0 cZero (by decide)).trans hc0)
      (by dsimp only [x₄]; wram_simp; exact (hx₃_fr0 cOne (by decide)).trans hc1)
      (by dsimp only [x₄]; wram_simp; exact (hx₃_fr0 curB (by decide)).trans hcur)
      (by dsimp only [x₄]; wram_simp)
      (by dsimp only [x₄]; wram_simp; exact (hx₃_fr0 nVerts (by decide)).trans hNv)
      hx₃_deg
  have hx₅_comp : x₅.regs compIdxReg = kOffAddr wb :=
    (hx₅_ex.regs_eq (by decide)).trans (by dsimp only [x₄]; wram_simp)
  have hx₅_fr0 : ∀ r : Fin 28, r.val < 18 → r ≠ offB → x₅.regs r = x.regs r := fun r hr hno => by
    rw [hx₅_fr r hr]
    dsimp only [x₄]
    have hne_c : r ≠ compIdxReg := by reg_ne
    rw [Data.set_regs_of_ne hno, Data.set_regs_of_ne hne_c]
    exact hx₃_fr0 r hr
  let x₆ := (((x₅.set offB (kOffAddr wb)).set finCnt (kEdgeAddr wb N)).set
    edgeB (kRevEdgeAddr wb N Mc)).set uReg 0
  have hp3 : ExecWithin (B := .standard) w
      (ram[ offB ← compIdxReg; finCnt ← edgeB; edgeB ← revEdgeB; uReg ← cZero ]) x₅ x₆ 4 := by
    have h_eb : x₅.regs edgeB = kEdgeAddr wb N :=
      (hx₅_fr0 edgeB (by decide) (by decide)).trans hedge
    have h_reb : x₅.regs revEdgeB = kRevEdgeAddr wb N Mc :=
      (hx₅_fr0 revEdgeB (by decide) (by decide)).trans hredge
    have h_c0 : x₅.regs cZero = 0 := (hx₅_fr0 cZero (by decide) (by decide)).trans hc0
    wram_exec [hx₅_comp, h_eb, h_reb, h_c0]
  have hx₅_csr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x₅.mem :=
    hx₁_csr.of_eqOn
      (fun _ _ => (hx₅_out _ (by dsimp only [kOffAddr, kRevOffAddr, kCurAddr]; omega)).trans
        (hx₃_out _ (by dsimp only [kOffAddr, kCurAddr]; omega)))
      (fun _ _ => (hx₅_out _ (by dsimp only [kEdgeAddr, kRevOffAddr, kCurAddr]; omega)).trans
        (hx₃_out _ (by dsimp only [kEdgeAddr, kCurAddr]; omega)))
  obtain ⟨x₇, hx₇_ex, hx₇_pcsr, hx₇_out, hx₇_fr⟩ :=
    forEachArc_spec adj wb Mc hmc hfit finCnt uReg backfillStepCode 6 (fun z => (revAdj z).length)
      (fun rev mem => PartialCSRAt revAdj rev (kCurAddr wb N Mc) (kRevEdgeAddr wb N Mc) mem)
      (fun a => (kCurAddr wb N Mc ≤ a ∧ a < kCurAddr wb N Mc + N) ∨
        (kRevEdgeAddr wb N Mc ≤ a ∧ a < kRevEdgeAddr wb N Mc + csrOffset revAdj N))
      (fun d => d.regs curB = kCurAddr wb N Mc ∧ d.regs edgeB = kRevEdgeAddr wb N Mc)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun a ha => by
        dsimp only [kOffAddr, kEdgeAddr, kCurAddr, kRevEdgeAddr] at ha ⊢
        omega)
      (fun d₁ d₂ hd h => ⟨(hd curB (by decide)).symm ▸ h.1, (hd edgeB (by decide)).symm ▸ h.2⟩)
      (fun u v rev s hroom hinv hc1' hu hv ⟨hcur', hedge'⟩ =>
        backfillStepCode_spec revAdj rev (kCurAddr wb N Mc) (kRevEdgeAddr wb N Mc) Mc
          (by simp only [kRevEdgeAddr, kCurAddr]; omega) hmc_rev hf_cur v u hroom
          hc1' hcur' hedge' hv hu hinv)
      (List.finRange N) 0 (fun _ => []) x₆ (by simp) (fun q _ => by simp) (fun _ => le_rfl)
      (partialCSRAt_init revAdj (kCurAddr wb N Mc) (kRevEdgeAddr wb N Mc) x₅.mem hx₅_cur)
      hx₅_csr
      (by dsimp only [x₆]; wram_simp; exact (hx₅_fr0 cOne (by decide) (by decide)).trans hc1)
      (by dsimp only [x₆]; wram_simp; exact (hx₅_fr0 nVerts (by decide) (by decide)).trans hNv)
      (by dsimp only [x₆]; wram_simp)
      (by dsimp only [x₆]; wram_simp)
      ⟨by dsimp only [x₆]; wram_simp; exact (hx₅_fr0 curB (by decide) (by decide)).trans hcur,
        by dsimp only [x₆]; wram_simp⟩
      (by dsimp only [x₆]; wram_simp)
  have hx₇_roff : ∀ u ≤ N, x₇.mem (kRevOffAddr wb N Mc + u) = csrOffset revAdj u := fun u hu => by
    rw [hx₇_out _ (by simp only [kRevOffAddr, kCurAddr, kRevEdgeAddr]; omega)]
    exact hx₅_roff u hu
  have hx₇_rcsr : CSRAt revAdj (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc) x₇.mem :=
    csrAt_of_partialCSRAt revAdj (kRevOffAddr wb N Mc) (kCurAddr wb N Mc) (kRevEdgeAddr wb N Mc)
      x₇.mem hx₇_roff hx₇_pcsr
  have hx₇_rob : x₇.regs revOffB = kRevOffAddr wb N Mc := by
    rw [hx₇_fr revOffB (by decide)]
    dsimp only [x₆]; wram_simp
    exact (hx₅_fr0 revOffB (by decide) (by decide)).trans hroff
  let y := x₇.set offB (kRevOffAddr wb N Mc)
  have hp4 : ExecWithin (B := .standard) w (ram[ offB ← revOffB ]) x₇ y 1 := by
    wram_exec [hx₇_rob]
  have hout_sum : outDegreeSum adj (List.finRange N) = csrOffset adj N :=
    (csrOffset_eq_outDegreeSum adj).symm
  rw [List.length_finRange, hout_sum] at hx₃_ex hx₇_ex
  refine ⟨y,
    (hx₁_ex.seq (hp1.seq (hx₃_ex.seq (hp2.seq (hx₅_ex.seq (hp3.seq (hx₇_ex.seq hp4))))))).mono
      (by omega),
    hx₇_rcsr,
    by dsimp only [y]; wram_simp,
    by
      dsimp only [y]; wram_simp
      rw [hx₇_fr edgeB (by decide)]; dsimp only [x₆]; wram_simp,
    fun a ha => ?_,
    fun r hr hno hne => ?_⟩
  · dsimp only [y]; mem_upd
    rw [hx₇_out _ (by dsimp only [revAdj, revGraph] at *; omega)]
    dsimp only [x₆]; mem_upd
    rw [hx₅_out _ (by omega)]
    dsimp only [x₄]; mem_upd
    rw [hx₃_out _ (by omega)]
    dsimp only [x₂]; mem_upd
    exact hx₁_out _ (by omega)
  · dsimp only [y]
    rw [Data.set_regs_of_ne hno, hx₇_fr r hr]
    dsimp only [x₆]
    have hne_u : r ≠ uReg := by reg_ne
    have hne_fc : r ≠ finCnt := by reg_ne
    rw [Data.set_regs_of_ne hne_u, Data.set_regs_of_ne hne, Data.set_regs_of_ne hne_fc,
      Data.set_regs_of_ne hno]
    exact hx₅_fr0 r hr hno

/-! ### Pass 3: Kosaraju SCC peeling and component indexing (`O(N + M)`) -/

/-- Write the current component index for one newly finished vertex. -/
private def writeCompBody : Code .standard 28 := ram[
  addr ← finB + pReg; vReg ← *addr;
  addr ← compB + vReg; *addr ← compIdxReg;
  pReg ← pReg + cOne ]

/-- Kosaraju peeling step: visit the next vertex in reverse finishing order in the transpose and
index the vertices finished as one component. -/
private def peelStepBody : Code .standard 28 :=
  (ram[ addr ← nVerts - cOne; addr ← addr - iReg; addr ← ordB + addr; uReg ← *addr;
        oldFinReg ← finCnt ]).seq
    (visitRootCode.seq
      ((Code.branch (.lt oldFinReg finCnt)
          ((ram[ pReg ← oldFinReg ]).seq
            ((Code.loop (.lt pReg finCnt) writeCompBody).seq
              (ram[ compIdxReg ← compIdxReg + cOne ])))
          (ram[ compIdxReg ← compIdxReg ])).seq
        (ram[ iReg ← iReg + cOne ])))

/-- Second Kosaraju pass: peel the transpose in reverse finishing order, writing component indices
at `compB`. -/
def kosarajuIndexCode : Code .standard 28 :=
  (zeroBlockCode visB).seq
    ((ram[ finCnt ← cZero; compIdxReg ← cZero; iReg ← cZero ]).seq
      (.loop (.lt iReg nVerts) peelStepBody))

private theorem writeCompLoop_spec {N w : ℕ} (finAddr compAddr : ℕ) (hdisj : finAddr + N ≤ compAddr)
    (F₀ L cIdx : ℕ) (hFL : F₀ + L ≤ N) (hfit : Fits w (compAddr + N + 2))
    (comp : List (Fin N)) (hnd : comp.Nodup) (hlen : comp.length = L) :
    ∀ (rem k : ℕ) (f : Fin N → ℕ) (x : Data 28)
      (_ : k + rem = L),
      (∀ q (hq : q < L), x.mem (finAddr + F₀ + q) = (comp[q]'(hlen ▸ hq)).val) →
      (∀ u : Fin N, x.mem (compAddr + u.val) =
        if u ∈ comp.take k then cIdx else f u) →
      x.regs cOne = 1 → x.regs finB = finAddr → x.regs compB = compAddr →
      x.regs compIdxReg = cIdx → x.regs finCnt = F₀ + L → x.regs pReg = F₀ + k →
      ∃ y, ExecWithin w (.loop (.lt pReg finCnt) writeCompBody) x y (7 * rem + 2) ∧
        (∀ u : Fin N, y.mem (compAddr + u.val) = if u ∈ comp then cIdx else f u) ∧
        (∀ a, ¬ (compAddr ≤ a ∧ a < compAddr + N) → y.mem a = x.mem a) ∧
        (∀ r : Fin 28, r ≠ addr → r ≠ vReg → r ≠ pReg → y.regs r = x.regs r)
  | 0, k, f, x, hk, _, hf_mem, _, _, _, _, hfc, hp => by
    have hk_eq : k = L := by omega
    subst hk_eq
    have hend : ¬ (Cond.lt pReg finCnt).Holds x := by
      change ¬ x.regs pReg < x.regs finCnt; omega
    refine ⟨x, ⟨2, by simp, Exec.loop_exit hend⟩, fun u => ?_, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
    simpa [List.take_of_length_le (by omega : comp.length ≤ k)] using hf_mem u
  | rem + 1, k, f, x, hk, hfin_mem, hf_mem, hc1, hfb, hcb, hcIdx, hfc, hp => by
    have hk_lt : k < L := by omega
    set v := comp[k]'(by omega)
    have hm_v : x.mem (finAddr + (F₀ + k)) = v.val := by
      rw [← Nat.add_assoc]; exact hfin_mem k hk_lt
    have hf_fa : Fits w (finAddr + (F₀ + k)) := hfit.of_le (by omega)
    have hf_ca : Fits w (compAddr + v.val) := hfit.of_le (by have := v.isLt; omega)
    have hf_p1 : Fits w (F₀ + k + 1) := hfit.of_le (by omega)
    let StepPost (x₁ : Data 28) : Prop :=
      (∀ u : Fin N, x₁.mem (compAddr + u.val) =
          if u ∈ comp.take (k + 1) then cIdx else f u) ∧
        (∀ a, ¬ (compAddr ≤ a ∧ a < compAddr + N) → x₁.mem a = x.mem a) ∧
        x₁.regs pReg = F₀ + (k + 1) ∧
        (∀ r : Fin 28, r ≠ addr → r ≠ vReg → r ≠ pReg → x₁.regs r = x.regs r)
    have hstep : ∃ x₁, ExecWithin w writeCompBody x x₁ 5 ∧ StepPost x₁ := by
      unfold writeCompBody
      wram_exec [hc1, hfb, hcb, hcIdx, hp, hm_v, hf_fa, hf_ca, hf_p1]
      dsimp only [StepPost]
      refine ⟨fun u => ?_, fun a ha => ?_, by wram_simp; omega, fun r h1 h2 h3 => ?_⟩
      · mem_upd
        have htake : comp.take (k + 1) = comp.take k ++ [v] := by
          rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
          rfl
        rw [htake]
        by_cases huv : u = v
        · subst huv; simp
        · have hne : compAddr + u.val ≠ compAddr + v.val := fun h => huv (Fin.ext (by omega))
          rw [Function.update_of_ne hne, hf_mem u]
          simp [huv]
      · mem_upd
        exact Function.update_of_ne (by have := v.isLt; omega) _ _
      · regs_lt
    obtain ⟨x₁, hx₁_ex, hx₁_f, hx₁_out, hx₁_p, hx₁_fr⟩ := hstep
    have hfin_mem₁ : ∀ q (hq : q < L), x₁.mem (finAddr + F₀ + q) = (comp[q]'(hlen ▸ hq)).val :=
      fun q hq => (hx₁_out _ (by omega)).trans (hfin_mem q hq)
    obtain ⟨y, hy_ex, hy_f, hy_out, hy_fr⟩ :=
      writeCompLoop_spec finAddr compAddr hdisj F₀ L cIdx hFL hfit comp hnd hlen rem (k + 1) f x₁
        (by omega) hfin_mem₁ hx₁_f
        ((hx₁_fr cOne (by decide) (by decide) (by decide)).trans hc1)
        ((hx₁_fr finB (by decide) (by decide) (by decide)).trans hfb)
        ((hx₁_fr compB (by decide) (by decide) (by decide)).trans hcb)
        ((hx₁_fr compIdxReg (by decide) (by decide) (by decide)).trans hcIdx)
        ((hx₁_fr finCnt (by decide) (by decide) (by decide)).trans hfc)
        hx₁_p
    obtain ⟨t₁, ht₁, he₁⟩ := hx₁_ex
    obtain ⟨t₂, ht₂, he₂⟩ := hy_ex
    have hlt : (Cond.lt pReg finCnt).Holds x := by
      change x.regs pReg < x.regs finCnt; omega
    refine ⟨y, ⟨t₁ + t₂ + 2, by omega, Exec.loop_iter hlt he₁ he₂⟩,
      hy_f, fun a ha => (hy_out a ha).trans (hx₁_out a ha),
      fun r h1 h2 h3 => (hy_fr r h1 h2 h3).trans (hx₁_fr r h1 h2 h3)⟩

private theorem peelLoop_spec {N w : ℕ} (hN : 0 < N) (revAdj : Fin N → List (Fin N))
    (ord : List (Fin N)) (hord_len : ord.length = N)
    (wb Mc : ℕ) (hmc : csrOffset revAdj N ≤ Mc)
    (hfit : Fits w (kTopAddr wb N Mc + Mc + 4)) :
    ∀ (rs : List (Fin N)) (idx F₀ cIdx : ℕ) (vis : Finset (Fin N)) (f : Fin N → ℕ) (x : Data 28)
      (_ : idx + rs.length = N),
      (∀ q (hq : q < rs.length), rs[q] = ord[idx + q]'(by omega)) →
      F₀ = vis.card →
      cIdx ≤ F₀ →
      DfsRegs (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc) (kVisAddr wb N Mc) (kFinAddr wb N Mc)
        (kStkAddr wb N Mc) x →
      x.regs nVerts = N → x.regs ordB = kOrdAddr wb N Mc → x.regs compB = kCompAddr wb N Mc →
      x.regs iReg = idx → x.regs finCnt = F₀ → x.regs compIdxReg = cIdx →
      CSRAt revAdj (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc) x.mem →
      (∀ q (hq : q < N), x.mem (kOrdAddr wb N Mc + (N - 1 - q)) = (ord[q]'(by omega)).val) →
      VisAt vis (kVisAddr wb N Mc) x.mem →
      (∀ u : Fin N, u ∈ vis → x.mem (kCompAddr wb N Mc + u.val) = f u) →
      ∃ y,
        let comps := peelSCCs revAdj N vis rs
        ExecWithin w (.loop (.lt iReg nVerts) peelStepBody) x y
          (30 * rs.length + 68 * comps.flatten.length +
            36 * outDegreeSum revAdj comps.flatten + 2) ∧
        (∀ u : Fin N, u ∈ vis ∨ u ∈ comps.flatten →
          y.mem (kCompAddr wb N Mc + u.val) = indexComponentsAux cIdx comps f u) ∧
        (∀ a, a < kVisAddr wb N Mc → y.mem a = x.mem a) ∧
        (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r)
  | [], idx, F₀, cIdx, vis, f, x, hidx, _, _, _, _, _, _, _, _, _, _, _, _, _, hf_vis => by
    simp only [List.length_nil, Nat.add_zero] at hidx
    have hend : ¬ (Cond.lt iReg nVerts).Holds x := by
      change ¬ x.regs iReg < x.regs nVerts; omega
    refine ⟨x, ⟨2, by simp [peelSCCs, outDegreeSum], Exec.loop_exit hend⟩,
      fun u hu => ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    simp only [peelSCCs, List.flatten_nil, List.not_mem_nil, or_false] at hu
    simpa [peelSCCs, indexComponentsAux] using hf_vis u hu
  | r :: rs, idx, F₀, cIdx, vis, f, x, hidx, hrs, hF₀, hcIdx_le, hregs, hNv, hordB, hcompB,
      hi, hfc, hcIdx, hcsr, hord_mem, hvis, hf_vis => by
    simp only [List.length_cons] at hidx
    have hr_eq : r = ord[idx]'(by omega) := by
      have h0 := hrs 0 (by simp)
      simpa only [Nat.add_zero, List.getElem_cons_zero] using h0
    have hm_ord : x.mem (kOrdAddr wb N Mc + (N - 1 - idx)) = r.val := by
      rw [hr_eq]; exact hord_mem idx (by omega)
    have hcard_le : vis.card ≤ N := by have := Finset.card_le_univ vis; simpa using this
    have hcons : F₀ + (N - vis.card) ≤ N := by omega
    have hf_n1 : Fits w (N - 1) := hfit.of_le (by simp only [kTopAddr]; omega)
    have hf_sub : Fits w (N - 1 - idx) := hfit.of_le (by simp only [kTopAddr]; omega)
    have hf_oa : Fits w (kOrdAddr wb N Mc + (N - 1 - idx)) :=
      hfit.of_le (by simp only [kOrdAddr, kTopAddr]; omega)
    have hfit_stk : Fits w (kStkAddr wb N Mc + 3 * N + Mc + 4) :=
      hfit.of_le (by simp only [kStkAddr, kTopAddr]; omega)
    let x₁ := ((((x.set addr (N - 1)).set addr (N - 1 - idx)).set
      addr (kOrdAddr wb N Mc + (N - 1 - idx))).set uReg r.val).set oldFinReg F₀
    have hp1 : ExecWithin w
        (ram[ addr ← nVerts - cOne; addr ← addr - iReg; addr ← ordB + addr; uReg ← *addr;
              oldFinReg ← finCnt ]) x x₁ 5 := by
      have hc1 := hregs.cone
      have htriv : x₁ = ((((x.set addr (N - 1)).set addr (N - 1 - idx)).set
        addr (kOrdAddr wb N Mc + (N - 1 - idx))).set uReg r.val).set oldFinReg F₀ := rfl
      wram_exec [hNv, hc1, hi, hordB, hm_ord, hfc, hf_n1, hf_oa]
    obtain ⟨y₁, hy₁_ex, hy₁_r, hy₁_csr, hy₁_vis, hy₁_fc, hy₁_fin_mem, hy₁_out, hy₁_fr⟩ :=
      visitRootCode_spec hN revAdj (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc)
        (kVisAddr wb N Mc) (kFinAddr wb N Mc) (kStkAddr wb N Mc) Mc
        (by simp only [kRevOffAddr, kVisAddr]; omega)
        (by simp only [kRevEdgeAddr, kVisAddr]; omega)
        (by simp only [kVisAddr, kFinAddr]; omega)
        (by simp only [kFinAddr, kStkAddr]; omega)
        hmc hfit_stk r F₀ vis hcons (x := x₁)
        (dfsRegs_of_frame hregs fun reg hreg => by
          dsimp only [x₁]; regs_lt)
        hcsr hvis (by dsimp only [x₁]; wram_simp) (by dsimp only [x₁]; wram_simp; exact hfc)
    set s := visit revAdj N r ⟨vis, []⟩
    obtain ⟨hnd_s, hdis_s, hvis_s⟩ := visit_nil_struct revAdj N r vis
    have hcard_s : s.visited.card = vis.card + s.finished.length := card_visit_nil revAdj N r vis
    have hy₁_of : y₁.regs oldFinReg = F₀ :=
      (hy₁_fr oldFinReg (.inr (.inr rfl))).trans (by dsimp only [x₁]; wram_simp)
    have hy₁_cIdx : y₁.regs compIdxReg = cIdx :=
      (hy₁_fr compIdxReg (.inr (.inl rfl))).trans (by dsimp only [x₁]; wram_simp; exact hcIdx)
    have hy₁_i : y₁.regs iReg = idx :=
      (hy₁_fr iReg (.inl (by decide))).trans (by dsimp only [x₁]; wram_simp; exact hi)
    have hy₁_fr0 : ∀ reg : Fin 28, reg.val < 18 → y₁.regs reg = x.regs reg := fun reg hreg => by
      rw [hy₁_fr reg (.inl (by omega))]
      dsimp only [x₁]; regs_lt
    let f' : Fin N → ℕ :=
      if s.finished.isEmpty then f
      else s.finished.foldl (fun g v => Function.update g v cIdx) f
    let cIdx' : ℕ := if s.finished.isEmpty then cIdx else cIdx + 1
    have hf_i1 : Fits w (idx + 1) := hfit.of_le (by simp only [kTopAddr]; omega)
    have hbranch : ∃ y₂,
        ExecWithin w
          ((Code.branch (.lt oldFinReg finCnt)
              ((ram[ pReg ← oldFinReg ]).seq
                ((Code.loop (.lt pReg finCnt) writeCompBody).seq
                  (ram[ compIdxReg ← compIdxReg + cOne ])))
              (ram[ compIdxReg ← compIdxReg ])).seq
            (ram[ iReg ← iReg + cOne ]))
          y₁ y₂ (7 * s.finished.length + 7) ∧
        y₂.regs iReg = idx + 1 ∧ y₂.regs finCnt = F₀ + s.finished.length ∧
        y₂.regs compIdxReg = cIdx' ∧
        (∀ u : Fin N, u ∈ s.visited → y₂.mem (kCompAddr wb N Mc + u.val) = f' u) ∧
        (∀ a, ¬ (kCompAddr wb N Mc ≤ a ∧ a < kCompAddr wb N Mc + N) → y₂.mem a = y₁.mem a) ∧
        (∀ reg : Fin 28, reg.val < 18 → y₂.regs reg = y₁.regs reg) := by
      have hFL : F₀ + s.finished.length ≤ N := by
        have := Finset.card_le_univ s.visited
        simp only [Fintype.card_fin] at this
        omega
      by_cases hempty : s.finished.isEmpty
      · have hlen0 : s.finished = [] := List.isEmpty_iff.1 hempty
        have hnlt : ¬ (Cond.lt oldFinReg finCnt).Holds y₁ := by
          change ¬ y₁.regs oldFinReg < y₁.regs finCnt
          simp [hy₁_of, hy₁_fc, hlen0]
        let y₂ := (y₁.set compIdxReg cIdx).set iReg (idx + 1)
        have hb : ExecWithin w
            (.branch (.lt oldFinReg finCnt)
              ((ram[ pReg ← oldFinReg ]).seq
                ((Code.loop (.lt pReg finCnt) writeCompBody).seq
                  (ram[ compIdxReg ← compIdxReg + cOne ])))
              (ram[ compIdxReg ← compIdxReg ]))
            y₁ (y₁.set compIdxReg cIdx) 3 := by
          have hnop : Exec (B := .standard) w (ram[ compIdxReg ← compIdxReg ])
              y₁ (y₁.set compIdxReg cIdx) 1 := by
            simpa [hy₁_cIdx] using
              Exec.op (B := .standard) (o := .copy compIdxReg compIdxReg) (x := y₁) (w := w) rfl
          exact ⟨3, le_rfl, Exec.branch_neg hnlt hnop⟩
        have hinc : ExecWithin w (ram[ iReg ← iReg + cOne ]) (y₁.set compIdxReg cIdx) y₂ 1 := by
          have hc1' := hy₁_r.cone
          wram_exec [hy₁_i, hc1', hf_i1]
        refine ⟨y₂, (hb.seq hinc).mono (by omega),
          by dsimp only [y₂]; wram_simp,
          by dsimp only [y₂]; wram_simp; exact hy₁_fc,
          by dsimp only [y₂, cIdx']; wram_simp; simp [hempty],
          fun u hu => ?_, fun _ _ => rfl, fun reg hreg => ?_⟩
        · dsimp only [y₂, f']; mem_upd
          simp only [hempty, ↓reduceIte]
          have huv : u ∈ vis := by simpa [s, hlen0] using (hvis_s u).1 hu
          rw [hy₁_out (kCompAddr wb N Mc + u.val) (by
            have := u.isLt
            dsimp only [s, kVisAddr, kFinAddr, kStkAddr, kCompAddr] at hFL ⊢
            omega)]
          exact hf_vis u huv
        · dsimp only [y₂]
          have hne1 : reg ≠ iReg := by reg_ne
          have hne2 : reg ≠ compIdxReg := by reg_ne
          simp [Data.set_regs_of_ne hne1, Data.set_regs_of_ne hne2]
      · have hpos : 0 < s.finished.length := by
          cases hs_eq : s.finished with
          | nil => simp [hs_eq] at hempty
          | cons _ _ => simp
        have hlt_br : (Cond.lt oldFinReg finCnt).Holds y₁ := by
          change y₁.regs oldFinReg < y₁.regs finCnt
          omega
        let z₀ := y₁.set pReg F₀
        have hp_z₀ : ExecWithin (B := .standard) w (ram[ pReg ← oldFinReg ]) y₁ z₀ 1 := by
          wram_exec [hy₁_of]
        have hf_comp : Fits w (kCompAddr wb N Mc + N + 2) :=
          hfit.of_le (by simp only [kCompAddr, kTopAddr]; omega)
        obtain ⟨z₁, hz₁_ex, hz₁_mem, hz₁_out, hz₁_fr⟩ :=
          writeCompLoop_spec (kFinAddr wb N Mc) (kCompAddr wb N Mc)
            (by simp only [kFinAddr, kCompAddr]; omega) F₀ s.finished.length cIdx hFL hf_comp
            s.finished.reverse (List.nodup_reverse.2 hnd_s) (by simp) s.finished.length 0
            (fun u => y₁.mem (kCompAddr wb N Mc + u.val)) z₀ (by simp)
            (fun q hq => by dsimp only [z₀]; exact hy₁_fin_mem q (by simpa using hq))
            (fun u => by dsimp only [z₀]; simp)
            (by dsimp only [z₀]; wram_simp; exact hy₁_r.cone)
            (by dsimp only [z₀]; wram_simp; exact hy₁_r.hfin)
            (by dsimp only [z₀]; wram_simp; exact (hy₁_fr0 compB (by decide)).trans hcompB)
            (by dsimp only [z₀]; wram_simp; exact hy₁_cIdx)
            (by dsimp only [z₀]; wram_simp; exact hy₁_fc)
            (by dsimp only [z₀]; wram_simp)
        have hz₁_cIdx : z₁.regs compIdxReg = cIdx :=
          (hz₁_fr compIdxReg (by decide) (by decide) (by decide)).trans
            (by dsimp only [z₀]; wram_simp; exact hy₁_cIdx)
        have hz₁_1 : z₁.regs cOne = 1 :=
          (hz₁_fr cOne (by decide) (by decide) (by decide)).trans
            (by dsimp only [z₀]; wram_simp; exact hy₁_r.cone)
        have hz₁_i : z₁.regs iReg = idx :=
          (hz₁_fr iReg (by decide) (by decide) (by decide)).trans
            (by dsimp only [z₀]; wram_simp; exact hy₁_i)
        have hf_c1 : Fits w (cIdx + 1) := hfit.of_le (by simp only [kTopAddr]; omega)
        let y₂ := (z₁.set compIdxReg (cIdx + 1)).set iReg (idx + 1)
        have hp_tail : ExecWithin w
            ((ram[ compIdxReg ← compIdxReg + cOne ]).seq (ram[ iReg ← iReg + cOne ]))
            z₁ y₂ 2 := by
          have htriv : y₂ = (z₁.set compIdxReg (cIdx + 1)).set iReg (idx + 1) := rfl
          wram_exec [hz₁_cIdx, hz₁_1, hz₁_i, hf_c1, hf_i1]
        obtain ⟨tb, htb, heb⟩ := hp_z₀.seq (hz₁_ex.seq
          (show ExecWithin w (ram[ compIdxReg ← compIdxReg + cOne ]) z₁
              (z₁.set compIdxReg (cIdx + 1)) 1 by wram_exec [hz₁_cIdx, hz₁_1, hf_c1]))
        have hbr_ex : ExecWithin w
            (.branch (.lt oldFinReg finCnt)
              ((ram[ pReg ← oldFinReg ]).seq
                ((Code.loop (.lt pReg finCnt) writeCompBody).seq
                  (ram[ compIdxReg ← compIdxReg + cOne ])))
              (ram[ compIdxReg ← compIdxReg ]))
            y₁ (z₁.set compIdxReg (cIdx + 1)) (7 * s.finished.length + 5) :=
          ⟨tb + 1, by omega, Exec.branch_pos hlt_br heb⟩
        have hinc_i : ExecWithin w (ram[ iReg ← iReg + cOne ])
            (z₁.set compIdxReg (cIdx + 1)) y₂ 1 := by
          wram_exec [hz₁_i, hz₁_1, hf_i1]
        refine ⟨y₂, (hbr_ex.seq hinc_i).mono (by omega),
          by dsimp only [y₂]; wram_simp,
          by
            dsimp only [y₂]; wram_simp
            exact (hz₁_fr finCnt (by decide) (by decide) (by decide)).trans
              (by dsimp only [z₀]; wram_simp; exact hy₁_fc),
          by dsimp only [y₂, cIdx']; wram_simp; simp [hempty],
          fun u hu => ?_, fun a ha => hz₁_out a ha, fun reg hreg => ?_⟩
        · dsimp only [y₂, f']; mem_upd
          simp only [hempty, Bool.false_eq_true, ↓reduceIte, hz₁_mem u, List.mem_reverse,
            foldl_update_const]
          by_cases huf : u ∈ s.finished
          · simp [huf]
          · simp only [huf, ↓reduceIte]
            have huv : u ∈ vis := ((hvis_s u).1 hu).resolve_right huf
            rw [hy₁_out (kCompAddr wb N Mc + u.val) (by
              have := u.isLt; dsimp only [kVisAddr, kFinAddr, kStkAddr, kCompAddr]; omega)]
            exact hf_vis u huv
        · dsimp only [y₂]
          have hne1 : reg ≠ iReg := by reg_ne
          have hne2 : reg ≠ compIdxReg := by reg_ne
          have hne3 : reg ≠ addr := by reg_ne
          have hne4 : reg ≠ vReg := by reg_ne
          have hne5 : reg ≠ pReg := by reg_ne
          rw [Data.set_regs_of_ne hne1, Data.set_regs_of_ne hne2, hz₁_fr reg hne3 hne4 hne5]
          dsimp only [z₀]
          exact Data.set_regs_of_ne hne5 _
    obtain ⟨y₂, hy₂_ex, hy₂_i, hy₂_fc, hy₂_cIdx, hy₂_comp, hy₂_out, hy₂_fr⟩ := hbranch
    have hy₂_fr0 : ∀ reg : Fin 28, reg.val < 18 → y₂.regs reg = x.regs reg :=
      fun reg hreg => (hy₂_fr reg hreg).trans (hy₁_fr0 reg hreg)
    have hy₂_csr : CSRAt revAdj (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc) y₂.mem :=
      hy₁_csr.of_eqOn
        (fun _ _ => hy₂_out _ (by dsimp only [kRevOffAddr, kCompAddr]; omega))
        (fun _ _ => hy₂_out _ (by dsimp only [kRevEdgeAddr, kCompAddr]; omega))
    have hy₂_ord : ∀ q (hq : q < N), y₂.mem (kOrdAddr wb N Mc + (N - 1 - q)) =
        (ord[q]'(by omega)).val := fun q hq => by
      rw [hy₂_out _ (by simp only [kOrdAddr, kCompAddr]; omega),
        hy₁_out _ (by simp only [kVisAddr, kOrdAddr, kFinAddr, kStkAddr]; omega)]
      exact hord_mem q hq
    have hy₂_vis : VisAt s.visited (kVisAddr wb N Mc) y₂.mem := fun z => by
      rw [hy₂_out _ (by have := z.isLt; simp only [kVisAddr, kCompAddr]; omega)]
      exact hy₁_vis z
    have hcIdx'_le : cIdx' ≤ F₀ + s.finished.length := by
      dsimp only [cIdx']
      split_ifs with he
      · omega
      · have hpos : 0 < s.finished.length := by
          cases hs_eq : s.finished with
          | nil => simp [hs_eq] at he
          | cons _ _ => simp
        omega
    obtain ⟨y, hy_ex, hy_comp, hy_out, hy_fr⟩ :=
      peelLoop_spec hN revAdj ord hord_len wb Mc hmc hfit rs (idx + 1)
        (F₀ + s.finished.length) cIdx' s.visited f' y₂ (by omega)
        (fun q hq => by
          have h := hrs (q + 1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 q] using h)
        (by omega) hcIdx'_le
        (dfsRegs_of_frame hy₁_r hy₂_fr)
        ((hy₂_fr0 nVerts (by decide)).trans hNv)
        ((hy₂_fr0 ordB (by decide)).trans hordB)
        ((hy₂_fr0 compB (by decide)).trans hcompB)
        hy₂_i hy₂_fc hy₂_cIdx hy₂_csr hy₂_ord hy₂_vis hy₂_comp
    have hbody_ex : ExecWithin w peelStepBody x y₂
        (28 + 67 * s.finished.length + 36 * outDegreeSum revAdj s.finished) :=
      (hp1.seq (hy₁_ex.seq hy₂_ex)).mono (by omega)
    obtain ⟨t₁, ht₁, he₁⟩ := hbody_ex
    obtain ⟨t₂, ht₂, he₂⟩ := hy_ex
    have hlt : (Cond.lt iReg nVerts).Holds x := by
      change x.regs iReg < x.regs nVerts; omega
    refine ⟨y, ⟨t₁ + t₂ + 2, ?_, Exec.loop_iter hlt he₁ he₂⟩,
      fun u hu => ?_, fun a ha => ?_, fun reg hreg => (hy_fr reg hreg).trans (hy₂_fr0 reg hreg)⟩
    · rw [peelSCCs, show visit revAdj N r ⟨vis, []⟩ = s from rfl]
      split_ifs with he
      · have hlen0 : s.finished = [] := List.isEmpty_iff.1 he
        simp only [hlen0, List.length_nil, outDegreeSum, List.map_nil, List.sum_nil] at ht₁
        simp only [List.length_cons]
        omega
      · simp only [List.length_cons, List.flatten_cons, List.length_append,
          outDegreeSum_append]
        omega
    · rw [peelSCCs, show visit revAdj N r ⟨vis, []⟩ = s from rfl] at hu ⊢
      split_ifs with he
      · simp only [he, ↓reduceIte] at hu
        dsimp only [cIdx', f'] at hy_comp
        simp only [he, ↓reduceIte] at hy_comp
        exact hy_comp u (hu.imp (fun h => (hvis_s u).2 (.inl h)) id)
      · simp only [he, Bool.false_eq_true, ↓reduceIte] at hu
        dsimp only [cIdx', f', indexComponentsAux] at hy_comp ⊢
        simp only [he, Bool.false_eq_true, ↓reduceIte] at hy_comp
        refine hy_comp u ?_
        rcases hu with huv | hflat
        · exact .inl ((hvis_s u).2 (.inl huv))
        · rcases List.mem_append.1 (by rwa [List.flatten_cons] at hflat) with huf | hrest
          · exact .inl ((hvis_s u).2 (.inr huf))
          · exact .inr hrest
    · rw [hy_out a ha, hy₂_out a (by dsimp only [kVisAddr, kCompAddr] at *; omega),
        hy₁_out a (by dsimp only [kVisAddr, kFinAddr, kStkAddr] at *; omega)]
      dsimp only [x₁]; mem_upd

theorem kosarajuIndexCode_spec {N w : ℕ} (hN : 0 < N) (adj : Fin N → List (Fin N))
    (wb Mc : ℕ) (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (kTopAddr wb N Mc + Mc + 4)) {x : Data 28}
    (hregs : DfsRegs (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc) (kVisAddr wb N Mc)
      (kFinAddr wb N Mc) (kStkAddr wb N Mc) x)
    (hNv : x.regs nVerts = N) (hordB : x.regs ordB = kOrdAddr wb N Mc)
    (hcompB : x.regs compB = kCompAddr wb N Mc)
    (hcsr : CSRAt (transposeAdj adj (List.finRange N))
      (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc) x.mem)
    (hord_len : (topologicalSort adj (List.finRange N)).length = N)
    (hord_mem : ∀ idx (hidx : idx < N),
      x.mem (kOrdAddr wb N Mc + (N - 1 - idx)) =
        ((topologicalSort adj (List.finRange N))[idx]'(by
          rw [length_topologicalSort_finRange]; exact hidx)).val) :
    ∃ y, ExecWithin w kosarajuIndexCode x y (102 * N + 36 * Mc + 9) ∧
      (∀ u : Fin N, y.mem (kCompAddr wb N Mc + u.val) =
        indexComponents (sccs adj (List.finRange N)) u) ∧
      (∀ a, a < kVisAddr wb N Mc → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r) := by
  set revAdj := transposeAdj adj (List.finRange N)
  set ord := topologicalSort adj (List.finRange N)
  have hmc_rev : csrOffset revAdj N ≤ Mc := by
    dsimp only [revAdj]; rwa [csrOffset_transposeAdj_eq]
  have hfit_vis : Fits w (kVisAddr wb N Mc + N) :=
    hfit.of_le (by simp only [kVisAddr, kTopAddr]; omega)
  obtain ⟨x₁, hx₁_ex, hx₁_zero, hx₁_out, hx₁_fr⟩ :=
    zeroBlockCode_spec visB (by decide) (kVisAddr wb N Mc) N hfit_vis
      hregs.czero hregs.cone hregs.hvis hNv
  have hx₁_csr : CSRAt revAdj (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc) x₁.mem :=
    hcsr.of_eqOn
      (fun _ _ => hx₁_out _ (by dsimp only [kRevOffAddr, kVisAddr]; omega))
      (fun _ _ => hx₁_out _ (by dsimp only [kRevEdgeAddr, kVisAddr]; omega))
  have hx₁_ord : ∀ idx (hidx : idx < N),
      x₁.mem (kOrdAddr wb N Mc + (N - 1 - idx)) =
        (ord[idx]'(by rw [hord_len]; exact hidx)).val :=
    fun idx hidx =>
      (hx₁_out _ (by dsimp only [kVisAddr, kOrdAddr]; omega)).trans (hord_mem idx hidx)
  have hx₁_vis : VisAt (∅ : Finset (Fin N)) (kVisAddr wb N Mc) x₁.mem := fun u => by
    simp [hx₁_zero u.val u.isLt]
  let x₂ := ((x₁.set finCnt 0).set compIdxReg 0).set iReg 0
  have hp : ExecWithin (B := .standard) w
      (ram[ finCnt ← cZero; compIdxReg ← cZero; iReg ← cZero ]) x₁ x₂ 3 := by
    have hc0 : x₁.regs cZero = 0 := (hx₁_fr cZero (by decide)).trans hregs.czero
    wram_exec [hc0]
  have hx₂_fr0 : ∀ r : Fin 28, r.val < 18 → x₂.regs r = x.regs r := fun r hr => by
    have h1 : r ≠ iReg := by reg_ne
    have h2 : r ≠ compIdxReg := by reg_ne
    have h3 : r ≠ finCnt := by reg_ne
    dsimp only [x₂]
    rw [Data.set_regs_of_ne h1, Data.set_regs_of_ne h2, Data.set_regs_of_ne h3]
    exact hx₁_fr r hr
  obtain ⟨y, hy_ex, hy_comp, hy_out, hy_fr⟩ :=
    peelLoop_spec hN revAdj ord hord_len wb Mc hmc_rev hfit ord 0 0 0 ∅ (fun _ => 0) x₂
      (by omega) (fun q _ => by simp) rfl (le_refl 0)
      (dfsRegs_of_frame hregs hx₂_fr0)
      ((hx₂_fr0 nVerts (by decide)).trans hNv)
      ((hx₂_fr0 ordB (by decide)).trans hordB)
      ((hx₂_fr0 compB (by decide)).trans hcompB)
      (by dsimp only [x₂]; wram_simp)
      (by dsimp only [x₂]; wram_simp)
      (by dsimp only [x₂]; wram_simp)
      hx₁_csr hx₁_ord hx₁_vis (fun _ hu => by simp at hu)
  have hsccs_eq : peelSCCs revAdj N ∅ ord = sccs adj (List.finRange N) := by
    simp [sccs, revAdj, ord]
  have hcond : IsSCCCondensation adj (sccs adj (List.finRange N)) :=
    isSCCCondensation_sccs List.mem_finRange
  have hflat_len : (sccs adj (List.finRange N)).flatten.length = N := by
    simpa using hcond.length_flatten_eq_card
  have hout_flat : outDegreeSum revAdj (sccs adj (List.finRange N)).flatten = csrOffset adj N := by
    rw [outDegreeSum, ← List.sum_toFinset _ hcond.nodup_flatten]
    have huniv : (sccs adj (List.finRange N)).flatten.toFinset = Finset.univ := by
      ext v; simp [hcond.mem_flatten v]
    rw [huniv, sum_length_transposeAdj, ← csrOffset_eq_outDegreeSum]
  rw [hsccs_eq, hord_len, hflat_len, hout_flat] at hy_ex
  refine ⟨y, (hx₁_ex.seq (hp.seq hy_ex)).mono (by omega), fun u => ?_, fun a ha => ?_,
    fun r hr => (hy_fr r hr).trans (hx₂_fr0 r hr)⟩
  · rw [hsccs_eq] at hy_comp
    exact hy_comp u (.inr (hcond.mem_flatten u))
  · exact (hy_out a ha).trans (hx₁_out a (by omega))


/-! ### Forward DFS, transpose and Kosaraju peeling as one pass (`O(N + M)`) -/

/-- Kosaraju's strongly connected components on the CSR graph at `kOffAddr wb`: forward DFS
finishing order, CSR transpose, and peeling the transpose in reverse finishing order, writing the
topological component index of every vertex to `kCompAddr wb N Mc`. -/
def sccIndexCode : Code .standard 28 :=
  forwardDFSCode.seq
    (transposeCSRCode.seq
      ((ram[ finB ← ordB + nVerts ]).seq kosarajuIndexCode))

/-- `sccIndexCode` does not read the word width. -/
theorem not_readsWidth_sccIndexCode : ¬ sccIndexCode.ReadsWidth := by decide +kernel

/-- `sccIndexCode` is `rand`-free. -/
theorem isRandFree_sccIndexCode : sccIndexCode.IsRandFree := by decide +kernel

/-- **Kosaraju's algorithm on the word RAM in `O(N + M)` instructions.** From the scratch layout
based at `wb` (with a CSR graph `adj` of at most `Mc` arcs at `kOffAddr wb`), `sccIndexCode`
writes `indexComponents (sccs adj (List.finRange N)) u` to `kCompAddr wb N Mc + u` for every
vertex `u`, leaving memory below `wb` unchanged. -/
theorem sccIndexCode_spec {N w : ℕ} (hN : 0 < N) (adj : Fin N → List (Fin N))
    (wb Mc : ℕ) (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (kTopAddr wb N Mc + Mc + 4)) {x : Data 28}
    (hregs : DfsRegs (kOffAddr wb) (kEdgeAddr wb N) (kVisAddr wb N Mc) (kOrdAddr wb N Mc)
      (kStkAddr wb N Mc) x)
    (hNv : x.regs nVerts = N) (hcur : x.regs curB = kCurAddr wb N Mc)
    (hroff : x.regs revOffB = kRevOffAddr wb N Mc)
    (hredge : x.regs revEdgeB = kRevEdgeAddr wb N Mc)
    (hordB : x.regs ordB = kOrdAddr wb N Mc) (hcompB : x.regs compB = kCompAddr wb N Mc)
    (hcsr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x.mem) :
    ∃ y, ExecWithin w sccIndexCode x y (220 * N + 92 * Mc + 42) ∧
      (∀ u : Fin N, y.mem (kCompAddr wb N Mc + u.val) =
        indexComponents (sccs adj (List.finRange N)) u) ∧
      (∀ a, a < wb → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r.val < 18 → r ≠ offB → r ≠ edgeB → r ≠ finB → y.regs r = x.regs r) := by
  obtain ⟨s₁, hs₁_ex, hs₁_olen, hs₁_omem, hs₁_csr, hs₁_out, hs₁_fr⟩ :=
    forwardDFSCode_spec hN adj wb Mc hmc hfit hregs hNv hcsr
  obtain ⟨s₂, hs₂_ex, hs₂_rcsr, hs₂_off, hs₂_edge, hs₂_out, hs₂_fr⟩ :=
    transposeCSRCode_spec adj wb Mc hmc hfit
      ((hs₁_fr cZero (by decide)).trans hregs.czero)
      ((hs₁_fr cOne (by decide)).trans hregs.cone)
      ((hs₁_fr nVerts (by decide)).trans hNv)
      ((hs₁_fr offB (by decide)).trans hregs.hoff)
      ((hs₁_fr edgeB (by decide)).trans hregs.hedge)
      ((hs₁_fr curB (by decide)).trans hcur)
      ((hs₁_fr revOffB (by decide)).trans hroff)
      ((hs₁_fr revEdgeB (by decide)).trans hredge)
      hs₁_csr
  have hs₂_fr0 : ∀ r : Fin 28, r.val < 18 → r ≠ offB → r ≠ edgeB → s₂.regs r = x.regs r :=
    fun r hr hno hne => (hs₂_fr r hr hno hne).trans (hs₁_fr r hr)
  let s₃ := s₂.set finB (kFinAddr wb N Mc)
  have hs₃_ex : ExecWithin w (ram[ finB ← ordB + nVerts ]) s₂ s₃ 1 := by
    have h_ordB : s₂.regs ordB = kOrdAddr wb N Mc :=
      (hs₂_fr0 ordB (by decide) (by decide) (by decide)).trans hordB
    have h_Nv : s₂.regs nVerts = N :=
      (hs₂_fr0 nVerts (by decide) (by decide) (by decide)).trans hNv
    have htriv : s₃ = s₂.set finB (kOrdAddr wb N Mc + N) := by
      simp only [s₃, kOrdAddr, kFinAddr]; ring_nf
    rw [htriv]
    have hf_on : Fits w (kOrdAddr wb N Mc + N) :=
      hfit.of_le (by simp only [kOrdAddr, kTopAddr]; omega)
    wram_exec [h_ordB, h_Nv, hf_on]
  have hs₃_fr : ∀ r : Fin 28, r.val < 18 → r ≠ offB → r ≠ edgeB → r ≠ finB →
      s₃.regs r = x.regs r := fun r hr h1 h2 h3 => by
    simp only [s₃]
    rw [Data.set_regs_of_ne h3]
    exact hs₂_fr0 r hr h1 h2
  have hs₃_dregs : DfsRegs (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc)
      (kVisAddr wb N Mc) (kFinAddr wb N Mc) (kStkAddr wb N Mc) s₃ :=
    { czero := (hs₃_fr cZero (by decide) (by decide) (by decide) (by decide)).trans hregs.czero
      cone := (hs₃_fr cOne (by decide) (by decide) (by decide) (by decide)).trans hregs.cone
      cthree := (hs₃_fr cThree (by decide) (by decide) (by decide) (by decide)).trans hregs.cthree
      hoff := by simp only [s₃]; rw [Data.set_regs_of_ne (by decide)]; exact hs₂_off
      hedge := by simp only [s₃]; rw [Data.set_regs_of_ne (by decide)]; exact hs₂_edge
      hvis := (hs₃_fr visB (by decide) (by decide) (by decide) (by decide)).trans hregs.hvis
      hfin := Data.set_regs_self _ _ _
      hstk := (hs₃_fr stkB (by decide) (by decide) (by decide) (by decide)).trans hregs.hstk }
  have hs₃_omem : ∀ idx (hidx : idx < N),
      s₃.mem (kOrdAddr wb N Mc + (N - 1 - idx)) =
        ((topologicalSort adj (List.finRange N))[idx]'(by
          rw [length_topologicalSort_finRange]; exact hidx)).val :=
    fun idx hidx => by
      simp only [s₃]; mem_upd
      rw [hs₂_out _ (by dsimp only [kRevOffAddr, kRevEdgeAddr, kCurAddr, kOrdAddr]; omega)]
      exact hs₁_omem idx hidx
  obtain ⟨y, hy_ex, hy_comp, hy_out, hy_fr⟩ :=
    kosarajuIndexCode_spec hN adj wb Mc hmc hfit hs₃_dregs
      ((hs₃_fr nVerts (by decide) (by decide) (by decide) (by decide)).trans hNv)
      ((hs₃_fr ordB (by decide) (by decide) (by decide) (by decide)).trans hordB)
      ((hs₃_fr compB (by decide) (by decide) (by decide) (by decide)).trans hcompB)
      hs₂_rcsr hs₁_olen hs₃_omem
  refine ⟨y, (hs₁_ex.seq (hs₂_ex.seq (hs₃_ex.seq hy_ex))).mono (by omega), hy_comp,
    fun a ha => ?_, fun r hr h1 h2 h3 => (hy_fr r hr).trans (hs₃_fr r hr h1 h2 h3)⟩
  rw [hy_out a (by simp only [kVisAddr]; omega)]
  simp only [s₃]; mem_upd
  rw [hs₂_out a (by dsimp only [kRevOffAddr, kRevEdgeAddr, kCurAddr]; omega),
    hs₁_out a (by dsimp only [kVisAddr, kOrdAddr, kStkAddr]; omega)]

/-! ### Graphs in CSR form -/

/-- A directed multigraph on `Fin n` given by successor lists; parallel arcs and self-loops are
allowed. -/
structure Graph where
  /-- Number of vertices. -/
  n : ℕ
  /-- Successor lists. -/
  adj : Fin n → List (Fin n)

namespace Graph

/-- Number of arcs `∑ u, (G.adj u).length`. -/
@[expose] def m (G : Graph) : ℕ := csrOffset G.adj G.n

/-- **CSR (offset-array) input encoding** `[n, m, off 0, …, off n] ++ arcs`, where
`off u = csrOffset G.adj u` counts the arcs leaving vertices below `u` and `arcs` lists the
successors of `0, …, n - 1` in successor-list order. -/
@[expose] def encodeCSR (G : Graph) : List ℕ :=
  G.n :: G.m :: ((List.range (G.n + 1)).map (csrOffset G.adj) ++
    (List.finRange G.n).flatMap fun u => (G.adj u).map Fin.val)

/-- Linear word-size envelope `16 * (n + m + 1)` covering the input and the scratch layout. -/
@[expose] def wordBound (G : Graph) : ℕ := 16 * (G.n + G.m + 1)

private theorem length_flatMap_take {N : ℕ} (adj : Fin N → List (Fin N)) (u : ℕ) :
    (((List.finRange N).take u).flatMap fun v => (adj v).map Fin.val).length =
      csrOffset adj u := by
  simp [csrOffset, List.length_flatMap]

private theorem length_arcs (G : Graph) :
    ((List.finRange G.n).flatMap fun v => (G.adj v).map Fin.val).length = G.m := by
  have h := length_flatMap_take G.adj G.n
  rwa [List.take_of_length_le (by simp)] at h

private theorem getElem?_arcs {N : ℕ} (adj : Fin N → List (Fin N)) (u : Fin N) (k : ℕ)
    (hk : k < (adj u).length) :
    ((List.finRange N).flatMap fun v => (adj v).map Fin.val)[csrOffset adj u.val + k]? =
      some ((adj u)[k]).val := by
  have hsplit : List.finRange N =
      (List.finRange N).take u.val ++ u :: (List.finRange N).drop (u.val + 1) := by
    conv_lhs => rw [← List.take_append_drop u.val (List.finRange N)]
    rw [List.drop_eq_getElem_cons (by simp)]
    simp
  rw [hsplit, List.flatMap_append, List.flatMap_cons,
    List.getElem?_append_right (by rw [length_flatMap_take]; omega), length_flatMap_take,
    Nat.add_sub_cancel_left, List.getElem?_append_left (by simpa using hk)]
  simp [hk]

/-- The CSR input encoding installs `G.adj` as a CSR graph at `kOffAddr 3`. -/
theorem csrAt_init (G : Graph) :
    CSRAt G.adj (kOffAddr 3) (kEdgeAddr 3 G.n) (Data.init G.encodeCSR : Data 28).mem := by
  have hoffs : ((List.range (G.n + 1)).map (csrOffset G.adj)).length = G.n + 1 := by simp
  refine ⟨fun u hu => ?_, fun u k hk => ?_⟩
  · rw [show kOffAddr 3 + u = u + 2 + 1 by simp only [kOffAddr]; omega, Data.init_mem_succ,
      List.getD_eq_getElem?_getD]
    simp only [encodeCSR, List.getElem?_cons_succ]
    rw [List.getElem?_append_left (by rw [hoffs]; omega)]
    simp [Nat.lt_succ_of_le hu]
  · rw [show kEdgeAddr 3 G.n + csrOffset G.adj u.val + k =
        G.n + 1 + (csrOffset G.adj u.val + k) + 1 + 1 + 1 by simp only [kEdgeAddr]; omega,
      Data.init_mem_succ, List.getD_eq_getElem?_getD]
    simp only [encodeCSR, List.getElem?_cons_succ]
    rw [List.getElem?_append_right (by rw [hoffs]; omega), hoffs, Nat.add_sub_cancel_left,
      getElem?_arcs G.adj u k hk]
    rfl

/-- Every word of `G.encodeCSR`, and its length, fits any word width admitting
`G.wordBound`. -/
theorem inputFits_encodeCSR (G : Graph) {w : ℕ} (hfit : Fits w G.wordBound) :
    InputFits w G.encodeCSR := by
  refine ⟨hfit.of_le ?_, fun v hv => hfit.of_le ?_⟩
  · simp only [encodeCSR, List.length_cons, List.length_append, List.length_map,
      List.length_range, length_arcs, wordBound]
    omega
  · simp only [encodeCSR, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
      List.mem_flatMap] at hv
    rcases hv with rfl | rfl | ⟨a, ha, rfl⟩ | ⟨u, -, e, -, rfl⟩
    · unfold wordBound; omega
    · unfold wordBound; omega
    · have := csrOffset_mono G.adj (by omega : a ≤ G.n)
      unfold wordBound m; omega
    · have := e.isLt
      unfold wordBound; omega

end Graph

/-! ### End-to-end programs -/

/-- Load the constants, `n`, `m`, and the scratch layout based at `wb = 3` with `Mc = m`,
directly above the CSR input. -/
private def setupCode : Code .standard 28 := ram[
  cZero ← #0; cOne ← #1; cThree ← #3;
  nVerts ← *cOne; addr ← cOne + cOne; mArcs ← *addr;
  offB ← cThree;
  edgeB ← offB + nVerts; edgeB ← edgeB + cOne;
  revOffB ← edgeB + mArcs;
  revEdgeB ← revOffB + nVerts; revEdgeB ← revEdgeB + cOne;
  curB ← revEdgeB + mArcs;
  visB ← curB + nVerts; visB ← visB + cOne;
  ordB ← visB + nVerts;
  finB ← ordB;
  stkB ← ordB + nVerts; stkB ← stkB + nVerts;
  compB ← stkB + nVerts; compB ← compB + nVerts; compB ← compB + nVerts ]

private theorem setupCode_spec (G : Graph) {w : ℕ} (hfit : Fits w G.wordBound) :
    ∃ s, ExecWithin w setupCode (Data.init G.encodeCSR) s 23 ∧
      s.mem = (Data.init G.encodeCSR : Data 28).mem ∧
      s.regs outReg = 0 ∧ s.regs nVerts = G.n ∧
      DfsRegs (kOffAddr 3) (kEdgeAddr 3 G.n) (kVisAddr 3 G.n G.m) (kOrdAddr 3 G.n G.m)
        (kStkAddr 3 G.n G.m) s ∧
      s.regs curB = kCurAddr 3 G.n G.m ∧ s.regs revOffB = kRevOffAddr 3 G.n G.m ∧
      s.regs revEdgeB = kRevEdgeAddr 3 G.n G.m ∧ s.regs ordB = kOrdAddr 3 G.n G.m ∧
      s.regs compB = kCompAddr 3 G.n G.m := by
  have hm1 : (Data.init G.encodeCSR : Data 28).mem 1 = G.n := rfl
  have hm2 : (Data.init G.encodeCSR : Data 28).mem 2 = G.m := rfl
  let Post (s : Data 28) : Prop :=
    s.mem = (Data.init G.encodeCSR : Data 28).mem ∧
      s.regs outReg = 0 ∧ s.regs nVerts = G.n ∧
      DfsRegs (kOffAddr 3) (kEdgeAddr 3 G.n) (kVisAddr 3 G.n G.m) (kOrdAddr 3 G.n G.m)
        (kStkAddr 3 G.n G.m) s ∧
      s.regs curB = kCurAddr 3 G.n G.m ∧ s.regs revOffB = kRevOffAddr 3 G.n G.m ∧
      s.regs revEdgeB = kRevEdgeAddr 3 G.n G.m ∧ s.regs ordB = kOrdAddr 3 G.n G.m ∧
      s.regs compB = kCompAddr 3 G.n G.m
  change ∃ s, ExecWithin w setupCode (Data.init G.encodeCSR) s 23 ∧ Post s
  unfold setupCode
  wram_exec [Data.init_regs, hm1, hm2]
  · dsimp only [Post]
    refine ⟨rfl, by wram_simp; exact Data.init_regs _ _, ?_,
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    all_goals wram_simp
    all_goals
      dsimp only [kOffAddr, kEdgeAddr, kRevOffAddr, kRevEdgeAddr, kCurAddr, kVisAddr,
        kOrdAddr, kStkAddr, kCompAddr]
    all_goals omega
  all_goals exact hfit.of_le (by unfold Graph.wordBound; omega)

/-- One step of the reversed copy `out[i] := ord[N - 1 - i]`. -/
private def revCopyBody : Code .standard 28 := ram[
  addr ← nVerts - cOne; addr ← addr - iReg; addr ← ordB + addr; vReg ← *addr;
  addr ← outReg + iReg; addr ← addr + cOne; *addr ← vReg; iReg ← iReg + cOne ]

private theorem revCopyLoop_spec {N w : ℕ} (O P : ℕ) (hOP : O + N ≤ P)
    (hfit : Fits w (P + N + 1)) (f : ℕ → ℕ) :
    ∀ (rem k : ℕ) (x : Data 28) (_ : k + rem = N),
      (∀ q, q < N → x.mem (O + (N - 1 - q)) = f q) →
      (∀ q, q < k → x.mem (P + 1 + q) = f q) →
      x.regs cOne = 1 → x.regs nVerts = N → x.regs ordB = O → x.regs outReg = P →
      x.regs iReg = k →
      ∃ y, ExecWithin w (.loop (.lt iReg nVerts) revCopyBody) x y (10 * rem + 2) ∧
        (∀ q, q < N → y.mem (P + 1 + q) = f q) ∧
        (∀ a, a ≤ P → y.mem a = x.mem a) ∧
        (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r)
  | 0, k, x, hk, _, hcp, _, hNv, _, _, hi => by
    have hend : ¬ (Cond.lt iReg nVerts).Holds x := by
      change ¬ x.regs iReg < x.regs nVerts; omega
    exact ⟨x, ⟨2, by omega, Exec.loop_exit hend⟩, fun q hq => hcp q (by omega),
      fun _ _ => rfl, fun _ _ => rfl⟩
  | rem + 1, k, x, hk, hord, hcp, hc1, hNv, hO, hP, hi => by
    have hm : x.mem (O + (N - 1 - k)) = f k := hord k (by omega)
    have hf1 : Fits w (N - 1) := hfit.of_le (by omega)
    have hf2 : Fits w (N - 1 - k) := hfit.of_le (by omega)
    have hf3 : Fits w (O + (N - 1 - k)) := hfit.of_le (by omega)
    have hf4 : Fits w (P + k) := hfit.of_le (by omega)
    have hf5 : Fits w (P + k + 1) := hfit.of_le (by omega)
    have hf6 : Fits w (k + 1) := hfit.of_le (by omega)
    let StepPost (x₁ : Data 28) : Prop :=
      (∀ q, q < N → x₁.mem (O + (N - 1 - q)) = f q) ∧
        (∀ q, q < k + 1 → x₁.mem (P + 1 + q) = f q) ∧
        (∀ a, a ≤ P → x₁.mem a = x.mem a) ∧
        x₁.regs iReg = k + 1 ∧
        (∀ r : Fin 28, r.val < 18 → x₁.regs r = x.regs r)
    have hstep : ∃ x₁, ExecWithin w revCopyBody x x₁ 8 ∧ StepPost x₁ := by
      unfold revCopyBody
      wram_exec [hc1, hNv, hO, hP, hi, hm, hf1, hf2, hf3, hf4, hf5, hf6]
      dsimp only [StepPost]
      refine ⟨fun q hq => ?_, fun q hq => ?_, fun a ha => ?_, by wram_simp, fun r hr => ?_⟩
      · mem_upd
        rw [Function.update_of_ne (by omega)]
        exact hord q hq
      · mem_upd
        by_cases hqk : q = k
        · rw [hqk, show P + 1 + k = P + k + 1 by omega, Function.update_self]
        · rw [Function.update_of_ne (by omega)]
          exact hcp q (by omega)
      · mem_upd
        exact Function.update_of_ne (by omega) _ _
      · regs_lt
    obtain ⟨x₁, hx₁_ex, hx₁_ord, hx₁_cp, hx₁_low, hx₁_i, hx₁_fr⟩ := hstep
    obtain ⟨y, hy_ex, hy_cp, hy_low, hy_fr⟩ :=
      revCopyLoop_spec O P hOP hfit f rem (k + 1) x₁ (by omega) hx₁_ord hx₁_cp
        ((hx₁_fr cOne (by decide)).trans hc1) ((hx₁_fr nVerts (by decide)).trans hNv)
        ((hx₁_fr ordB (by decide)).trans hO) ((hx₁_fr outReg (by decide)).trans hP) hx₁_i
    obtain ⟨t₁, ht₁, he₁⟩ := hx₁_ex
    obtain ⟨t₂, ht₂, he₂⟩ := hy_ex
    have hlt : (Cond.lt iReg nVerts).Holds x := by
      change x.regs iReg < x.regs nVerts; omega
    exact ⟨y, ⟨t₁ + t₂ + 2, by omega, Exec.loop_iter hlt he₁ he₂⟩, hy_cp,
      fun a ha => (hy_low a ha).trans (hx₁_low a ha),
      fun r hr => (hy_fr r hr).trans (hx₁_fr r hr)⟩

/-- Topological-sort output: `topologicalSort G.adj (List.finRange G.n)` (the vertices in reverse
DFS finishing order) as vertex numbers. -/
@[expose] def topoWords (G : Graph) : List ℕ :=
  (topologicalSort G.adj (List.finRange G.n)).map Fin.val

/-- Strongly-connected-component output: the topological component index
`indexComponents (sccs G.adj (List.finRange G.n)) v` of each vertex `v = 0, …, n - 1`. -/
@[expose] def sccWords (G : Graph) : List ℕ :=
  (List.finRange G.n).map (indexComponents (sccs G.adj (List.finRange G.n)))

/-- Structured topological sort: setup, forward DFS, and reversed copy of the finishing order. -/
def topoCode : Code .standard 28 :=
  setupCode.seq
    (Code.branch (.eq nVerts cZero)
      (ram[ *cZero ← cZero ])
      (forwardDFSCode.seq
        ((ram[ outReg ← ordB + nVerts; *outReg ← nVerts; iReg ← cZero ]).seq
          (Code.loop (.lt iReg nVerts) revCopyBody))))

/-- Structured strongly-connected-component indexing: setup, then `sccIndexCode`. -/
def sccCode : Code .standard 28 :=
  setupCode.seq
    (Code.branch (.eq nVerts cZero)
      (ram[ *cZero ← cZero ])
      (sccIndexCode.seq (ram[ outReg ← compB - cOne; *outReg ← nVerts ])))

/-- Flat topological-sort program returning `topoWords G` via `ExecutesList`. -/
def topoProgram : Program .standard 28 := topoCode.program outReg

/-- Flat strongly-connected-component program returning `sccWords G` via `ExecutesList`. -/
def sccProgram : Program .standard 28 := sccCode.program outReg

private theorem n_eq_zero_branch {w : ℕ} {s : Data 28} (hs_out : s.regs outReg = 0)
    (hs_n : s.regs nVerts = 0) (hs_0 : s.regs cZero = 0) (pos : Code .standard 28) :
    ∃ y, ExecWithin w (Code.branch (.eq nVerts cZero) (ram[ *cZero ← cZero ]) pos) s y 2 ∧
      y.regs outReg = 0 ∧ outputList y.mem 0 = [] := by
  have hcond : (Cond.eq nVerts cZero).Holds s := by
    change s.regs nVerts = s.regs cZero; omega
  have hst : Exec (B := .standard) w (ram[ *cZero ← cZero ]) s (s.write 0 0) 1 := by
    have h := Exec.store (B := .standard) (w := w) (x := s) (a := cZero) (s := cZero)
    rwa [hs_0] at h
  refine ⟨s.write 0 0, ⟨2, le_rfl, Exec.branch_pos hcond hst⟩, hs_out, ?_⟩
  rw [outputList_eq_iff]
  exact ⟨Data.write_mem_self _ _ _, Block.holdsList_nil _ _⟩

private theorem topoWords_eq_nil (G : Graph) (hn0 : G.n = 0) : topoWords G = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [topoWords, List.length_map, length_topologicalSort_finRange, hn0]

private theorem sccWords_eq_nil (G : Graph) (hn0 : G.n = 0) : sccWords G = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [sccWords, List.length_map, List.length_finRange, hn0]

private theorem fits_top (G : Graph) {w : ℕ} (hfit : Fits w G.wordBound) :
    Fits w (kTopAddr 3 G.n G.m + G.m + 4) :=
  hfit.of_le (by simp only [kTopAddr, Graph.wordBound]; omega)

/-- **Linear-time topological sort on the word RAM.** From the CSR input `G.encodeCSR`, `topoCode`
leaves `topoWords G` (the reverse DFS finishing order, which by
`Cslib.Algorithms.Lean.DFS.isTopologicalOrder_topologicalSort_iff` is a topological order exactly
when `G` is acyclic) at the address in `outReg`, within `128 * (G.n + G.m + 1) - 1` instructions at
every word width `w` with `Fits w G.wordBound`. -/
theorem topoCode_spec (G : Graph) {w : ℕ} (hfit : Fits w G.wordBound) :
    ∃ y, ExecWithin w topoCode (Data.init G.encodeCSR) y (128 * (G.n + G.m + 1) - 1) ∧
      outputList y.mem (y.regs outReg) = topoWords G ∧
      Fits w (y.regs outReg + (topoWords G).length) := by
  obtain ⟨s, hs_ex, hs_mem, hs_out, hs_n, hs_r, -, -, -, hs_ord, -⟩ :=
    setupCode_spec G hfit
  by_cases hn0 : G.n = 0
  · obtain ⟨y, hy_ex, hy_out, hy_list⟩ :=
      n_eq_zero_branch hs_out (hs_n.trans hn0) hs_r.czero _
    refine ⟨y, (hs_ex.seq hy_ex).mono (by omega), ?_, ?_⟩
    · rw [hy_out, hy_list, topoWords_eq_nil G hn0]
    · rw [hy_out, topoWords_eq_nil G hn0]; exact fits_zero w
  have hN : 0 < G.n := Nat.pos_of_ne_zero hn0
  have hncond : ¬ (Cond.eq nVerts cZero).Holds s := by
    have := hs_r.czero
    change ¬ s.regs nVerts = s.regs cZero; omega
  have hfit_top := fits_top G hfit
  obtain ⟨s₁, hs₁_ex, -, hs₁_omem, -, -, hs₁_fr⟩ :=
    forwardDFSCode_spec hN G.adj 3 G.m le_rfl hfit_top hs_r hs_n (hs_mem ▸ G.csrAt_init)
  set O := kOrdAddr 3 G.n G.m with hO_def
  set P := O + G.n with hP_def
  have hP_fit : Fits w (P + G.n + 1) := hfit.of_le (by
    rw [hP_def, hO_def]; simp only [kOrdAddr, Graph.wordBound]; omega)
  let x₂ := ((s₁.set outReg P).write P G.n).set iReg 0
  have hs₂_ex : ExecWithin (B := .standard) w
      (ram[ outReg ← ordB + nVerts; *outReg ← nVerts; iReg ← cZero ]) s₁ x₂ 3 := by
    have h_ord : s₁.regs ordB = O := (hs₁_fr ordB (by decide)).trans hs_ord
    have h_n : s₁.regs nVerts = G.n := (hs₁_fr nVerts (by decide)).trans hs_n
    have h_0 : s₁.regs cZero = 0 := (hs₁_fr cZero (by decide)).trans hs_r.czero
    have hf_P : Fits w P := hP_fit.of_le (by omega)
    have htriv : x₂ = ((s₁.set outReg (O + G.n)).write (O + G.n) G.n).set iReg 0 := rfl
    wram_exec [h_ord, h_n, h_0, hf_P]
  have hlen : (topoWords G).length = G.n := by
    rw [topoWords, List.length_map, length_topologicalSort_finRange]
  obtain ⟨y, hy_ex, hy_cp, hy_low, hy_fr⟩ :=
    revCopyLoop_spec O P le_rfl hP_fit (fun q => (topoWords G).getD q 0) G.n 0 x₂ (by omega)
      (fun q hq => by
        simp only [x₂]; mem_upd
        rw [Function.update_of_ne (by omega), hs₁_omem q hq,
          List.getD_eq_getElem _ 0 (by rw [hlen]; exact hq)]
        simp [topoWords])
      (fun q hq => absurd hq (Nat.not_lt_zero q))
      (by simp only [x₂]; wram_simp; exact (hs₁_fr cOne (by decide)).trans hs_r.cone)
      (by simp only [x₂]; wram_simp; exact (hs₁_fr nVerts (by decide)).trans hs_n)
      (by simp only [x₂]; wram_simp; exact (hs₁_fr ordB (by decide)).trans hs_ord)
      (by simp only [x₂]; wram_simp)
      (by simp only [x₂]; wram_simp)
  have hy_out : y.regs outReg = P :=
    (hy_fr outReg (by decide)).trans (by simp only [x₂]; wram_simp)
  have hbr : ExecWithin w
      (Code.branch (.eq nVerts cZero) (ram[ *cZero ← cZero ])
        (forwardDFSCode.seq
          ((ram[ outReg ← ordB + nVerts; *outReg ← nVerts; iReg ← cZero ]).seq
            (Code.loop (.lt iReg nVerts) revCopyBody))))
      s y (97 * G.n + 36 * G.m + 17) := by
    obtain ⟨t, ht, he⟩ := (hs₁_ex.seq (hs₂_ex.seq hy_ex)).mono
      (show 87 * G.n + 36 * G.m + 10 + (3 + (10 * G.n + 2)) ≤ 97 * G.n + 36 * G.m + 15 by omega)
    exact ⟨t + 2, by omega, Exec.branch_neg hncond he⟩
  refine ⟨y, (hs_ex.seq hbr).mono (by omega), ?_, ?_⟩
  · rw [hy_out, outputList_eq_iff]
    refine ⟨?_, fun i => ?_⟩
    · rw [hy_low P le_rfl, hlen]
      simp only [x₂]; mem_upd
      rw [Function.update_self]
    · change y.mem (P + 1 + i.val) = (topoWords G)[i.val]
      have hi : i.val < G.n := by
        have h : i.val < (topoWords G).length := i.isLt
        omega
      rw [hy_cp i.val hi, List.getD_eq_getElem _ 0 (by exact i.isLt)]
  · rw [hy_out, hlen]; exact hP_fit.of_le (by omega)

/-- **Linear-time Kosaraju strongly connected components on the word RAM.** From the CSR input
`G.encodeCSR`, `sccCode` leaves `sccWords G` (each vertex's topological component index in
`Cslib.Algorithms.Lean.DFS.sccs`; by
`Cslib.Algorithms.Lean.DFS.IsSCCCondensation.indexComponents_eq_iff` two vertices receive the same
index exactly when they are strongly connected) at the address in `outReg`, within
`256 * (G.n + G.m + 1) - 1` instructions at every word width `w` with `Fits w G.wordBound`. -/
theorem sccCode_spec (G : Graph) {w : ℕ} (hfit : Fits w G.wordBound) :
    ∃ y, ExecWithin w sccCode (Data.init G.encodeCSR) y (256 * (G.n + G.m + 1) - 1) ∧
      outputList y.mem (y.regs outReg) = sccWords G ∧
      Fits w (y.regs outReg + (sccWords G).length) := by
  obtain ⟨s, hs_ex, hs_mem, hs_out, hs_n, hs_r, hs_cur, hs_roff, hs_redge, hs_ord, hs_comp⟩ :=
    setupCode_spec G hfit
  by_cases hn0 : G.n = 0
  · obtain ⟨y, hy_ex, hy_out, hy_list⟩ :=
      n_eq_zero_branch hs_out (hs_n.trans hn0) hs_r.czero _
    refine ⟨y, (hs_ex.seq hy_ex).mono (by omega), ?_, ?_⟩
    · rw [hy_out, hy_list, sccWords_eq_nil G hn0]
    · rw [hy_out, sccWords_eq_nil G hn0]; exact fits_zero w
  have hN : 0 < G.n := Nat.pos_of_ne_zero hn0
  have hncond : ¬ (Cond.eq nVerts cZero).Holds s := by
    have := hs_r.czero
    change ¬ s.regs nVerts = s.regs cZero; omega
  have hfit_top := fits_top G hfit
  obtain ⟨s₁, hs₁_ex, hs₁_comp, -, hs₁_fr⟩ :=
    sccIndexCode_spec hN G.adj 3 G.m le_rfl hfit_top hs_r hs_n hs_cur hs_roff hs_redge hs_ord
      hs_comp (hs_mem ▸ G.csrAt_init)
  set C := kCompAddr 3 G.n G.m with hC_def
  set P := C - 1 with hP_def
  have hC : C = P + 1 := by rw [hP_def, hC_def]; simp only [kCompAddr]; omega
  have hP_fit : Fits w (P + G.n + 1) := hfit.of_le (by
    rw [hP_def, hC_def]; simp only [kCompAddr, Graph.wordBound]; omega)
  let y := (s₁.set outReg P).write P G.n
  have hs₂_ex : ExecWithin (B := .standard) w (ram[ outReg ← compB - cOne; *outReg ← nVerts ])
      s₁ y 2 := by
    have h_c : s₁.regs compB = C :=
      (hs₁_fr compB (by decide) (by decide) (by decide) (by decide)).trans hs_comp
    have h_1 : s₁.regs cOne = 1 :=
      (hs₁_fr cOne (by decide) (by decide) (by decide) (by decide)).trans hs_r.cone
    have h_n : s₁.regs nVerts = G.n :=
      (hs₁_fr nVerts (by decide) (by decide) (by decide) (by decide)).trans hs_n
    have hf_P : Fits w P := hP_fit.of_le (by omega)
    have htriv : y = (s₁.set outReg (C - 1)).write (C - 1) G.n := rfl
    wram_exec [h_c, h_1, h_n, hf_P]
  have hlen : (sccWords G).length = G.n := by
    rw [sccWords, List.length_map, List.length_finRange]
  have hy_out : y.regs outReg = P := by simp only [y]; wram_simp
  have hbr : ExecWithin w
      (Code.branch (.eq nVerts cZero) (ram[ *cZero ← cZero ])
        (sccIndexCode.seq (ram[ outReg ← compB - cOne; *outReg ← nVerts ])))
      s y (220 * G.n + 92 * G.m + 46) := by
    obtain ⟨t, ht, he⟩ := hs₁_ex.seq hs₂_ex
    exact ⟨t + 2, by omega, Exec.branch_neg hncond he⟩
  refine ⟨y, (hs_ex.seq hbr).mono (by omega), ?_, ?_⟩
  · rw [hy_out, outputList_eq_iff]
    refine ⟨?_, fun i => ?_⟩
    · rw [hlen]; simp only [y]; mem_upd; rw [Function.update_self]
    · change y.mem (P + 1 + i.val) = (sccWords G)[i.val]
      have hi : i.val < G.n := by
        have h : i.val < (sccWords G).length := i.isLt
        omega
      simp only [y]; mem_upd
      rw [Function.update_of_ne (by omega), ← hC,
        show C + i.val = C + (⟨i.val, hi⟩ : Fin G.n).val from rfl, hs₁_comp ⟨i.val, hi⟩]
      simp [sccWords]
  · rw [hy_out, hlen]; exact hP_fit.of_le (by omega)

/-- `topoProgram` computes `topoWords` in `O(n + m)` instructions
(`Program.ComputesListInTime`). -/
theorem computesListInTime_topoProgram :
    topoProgram.ComputesListInTime (fun _ G => G.encodeCSR)
      (fun G _ => 128 * (G.n + G.m + 1)) (fun G w => Fits w G.wordBound) topoWords := by
  intro G w hfit _
  obtain ⟨y, ⟨steps, hsteps, hexec⟩, hylist, hyfit⟩ := topoCode_spec G hfit
  refine ⟨steps + 1, ?_, by dsimp only; omega⟩
  have hex := hexec.executesList outReg (by rwa [hylist])
  rwa [hylist] at hex

/-- `sccProgram` computes `sccWords` in `O(n + m)` instructions
(`Program.ComputesListInTime`). -/
theorem computesListInTime_sccProgram :
    sccProgram.ComputesListInTime (fun _ G => G.encodeCSR)
      (fun G _ => 256 * (G.n + G.m + 1)) (fun G w => Fits w G.wordBound) sccWords := by
  intro G w hfit _
  obtain ⟨y, ⟨steps, hsteps, hexec⟩, hylist, hyfit⟩ := sccCode_spec G hfit
  refine ⟨steps + 1, ?_, by dsimp only; omega⟩
  have hex := hexec.executesList outReg (by rwa [hylist])
  rwa [hylist] at hex

/-- `topoProgram` does not read the word width. -/
theorem not_readsWidth_topoProgram : ¬ topoProgram.ReadsWidth := by
  apply Code.not_readsWidth_program
  decide +kernel

/-- `topoProgram` is `rand`-free. -/
theorem isRandFree_topoProgram : topoProgram.IsRandFree := by
  rw [topoProgram, Code.isRandFree_program]
  decide +kernel

/-- `sccProgram` does not read the word width. -/
theorem not_readsWidth_sccProgram : ¬ sccProgram.ReadsWidth := by
  apply Code.not_readsWidth_program
  decide +kernel

/-- `sccProgram` is `rand`-free. -/
theorem isRandFree_sccProgram : sccProgram.IsRandFree := by
  rw [sccProgram, Code.isRandFree_program]
  decide +kernel

end Cslib.Algorithms.WordRAM.DFS
