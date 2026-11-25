/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.HopcroftKarp.Layout
public import CslibFrontier.Algorithms.WordRAM.HopcroftKarp.MatrixCSR
public import CslibFrontier.Computability.WordRAM.ListOutput
import CslibFrontier.Algorithms.WordRAM.HopcroftKarp.BFS
import CslibFrontier.Algorithms.WordRAM.HopcroftKarp.DFS
import CslibFrontier.Algorithms.WordRAM.HopcroftKarp.Internal
import CslibFrontier.Computability.WordRAM.Allocation
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.InputArray
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Foundations.Data.List.RowMajor
import Mathlib.Tactic.Linarith

/-!
# Hopcroft–Karp maximum bipartite matching on the word RAM

This file implements and proves machine-level running-time bounds on the standard-basis word RAM
(`Basis.standard`) for:

1. **Sparse Hopcroft–Karp (`O((m + r + |E|) √ν)`):** given a bipartite graph on `Fin m × Fin r`
   represented in compressed sparse row (CSR) format (`SparseInstance`), `coreCode` alternates
   queue-based breadth-first layering (`O(m + r + |E|)` instructions per round,
   `CslibFrontier.Algorithms.WordRAM.HopcroftKarp.BFS`) and iterative explicit-stack depth-first
   augmentation (`O(m + r + |E|)` instructions per phase,
   `CslibFrontier.Algorithms.WordRAM.HopcroftKarp.DFS`), matching the pure specification
   `Cslib.Algorithms.Lean.MaxFlow.hopcroftKarp` (`IsMaxMatching`, at most `2⌊√ν⌋` augmenting
   phases by `IsPhaseRun.le_two_mul_sqrt`). This yields end-to-end `State.init` programs for
   maximum matching (`sparseMatchingProgram`), matching cardinality (`sparseCardProgram`), and
   balanced perfect-matching decision (`sparsePerfectProgram`).
2. **Dense Hopcroft–Karp (`O((m + r)² √ν)`):** given an `m × r` `0/1` adjacency matrix
   (`DenseInstance`), converts the input matrix into exact CSR neighbour lists (`exactBipAdj`) in
   `O(m + m r)` instructions (`buildCSRCode` / `matrixSetupCode`,
   `CslibFrontier.Algorithms.WordRAM.HopcroftKarp.MatrixCSR`) and invokes `coreCode`, agreeing
   with `hopcroftKarpDense`.

The `O(n^{5/2})` Dilworth minimum chain cover and maximum antichain endpoints built on top of
`matrixSetupCode` and `coreCode` live in `CslibFrontier.Algorithms.WordRAM.ChainCover`.

## Main definitions

* `Cslib.Algorithms.WordRAM.HopcroftKarp.SparseInstance`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.DenseInstance`: sparse CSR and dense matrix problem
  instances with their word encodings, word-width envelopes, and outputs
  (`SparseInstance.matchingPairs`, `DenseInstance.matchingPairs`, `matchingWords`).
* `Cslib.Algorithms.WordRAM.HopcroftKarp.CSRMem`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.BaseRegs`: in-memory CSR layout and base-register frame
  for `coreCode`.
* `Cslib.Algorithms.WordRAM.HopcroftKarp.coreCode`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.buildCSRCode`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.matrixSetupCode`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.sparseMatchingProgram`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.sparseCardProgram`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.sparsePerfectProgram`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.denseMatchingProgram`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.denseCardProgram`: word-RAM subroutines and programs.
* `Cslib.Algorithms.WordRAM.HopcroftKarp.coreTime`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.sparseTime`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.sparseTimeSqrtMin`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.denseTime`: instruction bounds.

## Main results

* `Cslib.Algorithms.WordRAM.HopcroftKarp.core_exec`: in-memory CSR execution of Hopcroft–Karp in
  `O((m + r + |E|) (√ν + 1))` instructions.
* `Cslib.Algorithms.WordRAM.HopcroftKarp.exec_buildCSRCode`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.exec_matrixSetupCode`: dense/square `0/1`-matrix to CSR
  conversion in `O(m + m r)` instructions.
* `Cslib.Algorithms.WordRAM.HopcroftKarp.SparseInstance.getElem_matchingWords_even`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.SparseInstance.getElem_matchingWords_odd`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.DenseInstance.isMaxMatching_matchingPairs`: flat-word
  pair indexing and dense maximum-matching optimality.
* `Cslib.Algorithms.WordRAM.HopcroftKarp.executesList_sparseMatching`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.computesListInTime_sparseMatching`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.executes_sparseCard`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.decidesInTime_sparsePerfect`: sparse `O((m + r + |E|) √ν)`
  endpoints.
* `Cslib.Algorithms.WordRAM.HopcroftKarp.executesList_denseMatching`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.computesListInTime_denseMatching`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.executes_denseCard`: dense `O((m + r)² √ν)` endpoints.

## References

* [J. E. Hopcroft and R. M. Karp, *An n^{5/2} Algorithm for Maximum Matchings in Bipartite
  Graphs*][HopcroftKarp1973]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.WordRAM.HopcroftKarp

open Cslib.WordRAM
open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.MaxFlow
open Cslib.Algorithms.WordRAM.HopcroftKarp.Reg
open Cslib.Algorithms.WordRAM.HopcroftKarp.Internal

/-! ## Core Hopcroft–Karp phase loop (`coreCode`) -/

private abbrev fillConst (baseReg lenReg valReg : Fin 34) : Code .standard 34 :=
  Cslib.WordRAM.fillConst baseReg lenReg valReg one idx addr

private theorem exec_fillConst {w : ℕ} (baseReg lenReg valReg : Fin 34)
    (hb_lt : baseReg.val < 28) (hl_lt : lenReg.val < 28) (hv_lt : valReg.val < 28)
    (x : Data 34) (h1 : x.regs one = 1)
    (hfit_end : Fits w (x.regs baseReg + x.regs lenReg))
    (hfit_len : Fits w (x.regs lenReg)) :
    ∃ y, ExecWithin w (fillConst baseReg lenReg valReg) x y (5 * x.regs lenReg + 3) ∧
      (∀ i : Fin 34, i.val < 28 → y.regs i = x.regs i) ∧
      (∀ k < x.regs lenReg, y.mem (x.regs baseReg + k) = x.regs valReg) ∧
      (∀ a, ¬(x.regs baseReg ≤ a ∧ a < x.regs baseReg + x.regs lenReg) → y.mem a = x.mem a) := by
  have hne : ∀ j : Fin 34, j.val < 28 → idx ≠ j ∧ addr ≠ j := fun j hj =>
    ⟨fun h => by subst h; simp at hj, fun h => by subst h; simp at hj⟩
  obtain ⟨y, he, hr, _, hmem⟩ := Cslib.WordRAM.fillConst_exec (w := w)
    (base := baseReg) (len := lenReg) (val := valReg) (one := one) (idx := idx) (addr := addr)
    (hne baseReg hb_lt).1 (hne lenReg hl_lt).1 (hne valReg hv_lt).1 (by decide)
    (hne baseReg hb_lt).2 (hne lenReg hl_lt).2 (hne valReg hv_lt).2 (by decide) (by decide)
    h1 hfit_end hfit_len
  exact ⟨y, he.within, fun i hi => hr i (hne i hi).1.symm (hne i hi).2.symm,
    fun k hk => by rw [hmem]; exact fill_of_owns ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hk _⟩,
    fun a ha => by rw [hmem]; exact fill_of_not_owns ha⟩

private def phaseRoundBody : Code .standard 34 :=
  .seq bfsCode
    (.branch (.eq rfound one) dfsPhaseCode (ram[ phaseActive ← zero ]))

/-- In-memory Hopcroft–Karp solver on a CSR bipartite graph `inst` stored at `bOff`.
Initializes `colMate[0..r)` to `m` (`none`), then alternates `bfsCode` and `dfsPhaseCode` until
no augmenting path remains, leaving the maximum matching in `colMate[0..r)` and the closed
alternating-layer distances in `dist[0..m)`. -/
def coreCode : Code .standard 34 :=
  .seq (fillConst bColMateReg rr rm)
    (.seq (ram[ phaseActive ← one ])
      (.loop (.eq phaseActive one) phaseRoundBody))

private def roundTime (m r E : ℕ) : ℕ :=
  100 * m + 47 * r + 112 * E + 48

/-- Instruction bound `O((m + r + E) (√ν + 1))` for `coreCode` on a CSR graph with sides `m, r`,
`E` edge entries, and maximum matching cardinality `ν`. -/
@[expose] def coreTime (m r E ν : ℕ) : ℕ :=
  (2 * Nat.sqrt ν + 1) * (100 * m + 47 * r + 112 * E + 48) + 5 * r + 6

private theorem exec_phaseLoop {w bOff : ℕ} {inst : SparseInstance} :
    ∀ (fuel n : ℕ) (mate : Vector (Option (Fin inst.m)) inst.r),
      IsMatching inst.graph (mateMatching mate) →
      inst.m < fuel + (mateMatching mate).card →
      ∀ (x : Data 34),
        BaseRegs inst bOff x →
        CSRMem inst bOff x.mem →
        MateMem inst bOff mate x.mem →
        x.regs phaseActive = 1 →
        Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8) →
        let res := hkLoop inst.graph inst.adj fuel n mate
        ∃ y, ExecWithin w (.loop (.eq phaseActive one) phaseRoundBody) x y
            ((res.phases - n + 1) * roundTime inst.m inst.r inst.numEdges + 2) ∧
          (∀ i : Fin 34, i.val < 19 → y.regs i = x.regs i) ∧
          MateMem inst bOff res.mate y.mem ∧
          DistMem inst bOff res.dist y.mem ∧
          (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges ≤ a ∧
              a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
            y.mem a = x.mem a) := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ mate hM hfuel
    have := hM.card_le_card_left
    simp only [Fintype.card_fin] at this
    omega
  | succ fuel ih =>
    intro n mate hM hfuel x hb hcsr hmate hpa hfit
    have hc_loop : (Cond.eq phaseActive one).Holds x := by
      rw [Cond.holds_eq, hpa, hb.hone]
    obtain ⟨x₁, he_bfs, hr₁, hdM₁, hrk₁, hrf₁, hf₁⟩ := exec_bfsCode x hb hcsr hmate hfit
    set b := hkBfs inst.graph inst.adj mate with hb_def
    have hb₁ : BaseRegs inst bOff x₁ := hb.of_eq fun i hi => hr₁ i (by omega)
    have hcsr₁ : CSRMem inst bOff x₁.mem := hcsr.of_outside fun a ha => hf₁ a (by omega)
    have hmate₁ : MateMem inst bOff mate x₁.mem := hmate.of_outside fun a ha => hf₁ a (by omega)
    have hpa₁ : x₁.regs phaseActive = 1 := (hr₁ phaseActive (by decide)).trans hpa
    by_cases hbf : b.found = true
    · have hc_rf : (Cond.eq rfound one).Holds x₁ := by
        rw [Cond.holds_eq, hrf₁, hb₁.hone, ite_eq_left hbf]
      have hk_le : b.k ≤ inst.m + 1 := hkBfs_k_le inst.graph inst.adj mate
      obtain ⟨x₂, he_dfs, hr₂, hmate₂, hf₂⟩ :=
        exec_dfsPhaseCode hM hk_le x₁ hb₁ hcsr₁ hmate₁ hdM₁ hrk₁ hfit
      have he_br :=
        he_dfs.branch_pos (neg := (ram[ phaseActive ← zero ] : Code .standard 34)) hc_rf
      have hb_spec := hkBfs_spec inst.bipAdjValid_graph (mate := mate)
      rw [← hb_def] at hb_spec
      obtain ⟨N, hN, hmate_aug⟩ :=
        hkPhase_spec (k := b.k) (dist := b.dist) inst.bipAdjValid_graph hM hb_spec.exact
      obtain ⟨t, ht, hfree⟩ := hb_spec.found_true hbf
      have hM' : IsMatching inst.graph
          (mateMatching (hkPhase inst.graph inst.adj mate b.dist b.k)) :=
        hmate_aug ▸ hN.isMatching_augment hM
      have hcard_lt : (mateMatching mate).card <
          (mateMatching (hkPhase inst.graph inst.adj mate b.dist b.k)).card :=
        hmate_aug ▸ hN.card_lt_card_augment_of_mem_altRight hM hb_spec.noShort ht hfree
      have hb₂ : BaseRegs inst bOff x₂ := hb₁.of_eq fun i hi => hr₂ i (by omega)
      have hcsr₂ : CSRMem inst bOff x₂.mem := hcsr₁.of_outside fun a ha => hf₂ a (by omega)
      have hpa₂ : x₂.regs phaseActive = 1 := (hr₂ phaseActive (by decide)).trans hpa₁
      have hpost_phases := (hkLoop_spec inst.bipAdjValid_graph fuel (n + 1)
        (hkPhase inst.graph inst.adj mate b.dist b.k) hM' (by omega)).le_phases
      obtain ⟨y, he_rec, hr₃, hmate₃, hdM₃, hf₃⟩ :=
        ih (n + 1) (hkPhase inst.graph inst.adj mate b.dist b.k) hM' (by omega) x₂ hb₂ hcsr₂
          hmate₂ hpa₂ hfit
      dsimp only [hkLoop]
      rw [← hb_def, ite_eq_left hbf]
      set remPhases :=
        (hkLoop inst.graph inst.adj fuel (n + 1)
          (hkPhase inst.graph inst.adj mate b.dist b.k)).phases - (n + 1)
      have hph_arith :
          (hkLoop inst.graph inst.adj fuel (n + 1)
            (hkPhase inst.graph inst.adj mate b.dist b.k)).phases - n + 1 =
          (remPhases + 1) + 1 := by
        omega
      refine ⟨y, (ExecWithin.loop_iter hc_loop (he_bfs.seq he_br) he_rec).mono ?_,
        fun i hi => (hr₃ i hi).trans ((hr₂ i (by omega)).trans (hr₁ i (by omega))),
        hmate₃, hdM₃,
        fun a ha => (hf₃ a ha).trans ((hf₂ a ha).trans (hf₁ a (by omega)))⟩
      simp only [hph_arith, Nat.add_mul, Nat.one_mul, roundTime]
      omega
    · have hc_rf : ¬(Cond.eq rfound one).Holds x₁ := by
        rw [Cond.holds_eq, hrf₁, hb₁.hone, ite_eq_right hbf]
        simp
      have hstop : ExecWithin w (ram[ phaseActive ← zero ] : Code .standard 34)
          x₁ (x₁.set phaseActive 0) 1 := by
        refine WP.execWithin ?_
        wram_exec [hb₁.hzero]
        rfl
      have he_br := hstop.branch_neg (pos := dfsPhaseCode) hc_rf
      have hc_exit : ¬(Cond.eq phaseActive one).Holds (x₁.set phaseActive 0) := by
        rw [Cond.holds_eq]
        have ha0 : (x₁.set phaseActive 0).regs phaseActive = 0 := by wram_simp
        have ho1 : (x₁.set phaseActive 0).regs one = 1 := by wram_simp [hb₁.hone]
        omega
      have he_exit := ExecWithin.loop_exit (body := phaseRoundBody) (w := w) hc_exit
      dsimp only [hkLoop]
      rw [← hb_def, ite_eq_right hbf]
      refine ⟨x₁.set phaseActive 0,
        (ExecWithin.loop_iter hc_loop (he_bfs.seq he_br) he_exit).mono ?_,
        fun i hi => by wram_simp [hr₁ i (by omega)],
        hmate₁, hdM₁, fun a ha => hf₁ a (by omega)⟩
      change _ ≤ (n - n + 1) * roundTime inst.m inst.r inst.numEdges + 2
      simp only [Nat.sub_self, Nat.zero_add, Nat.one_mul, roundTime]
      omega

/-- **In-memory `O((m + r + |E|) (√ν + 1))` execution of Hopcroft–Karp (`coreCode`).**
Starting from any state `x` with `BaseRegs inst bOff x` and `CSRMem inst bOff x.mem`, `coreCode`
terminates within `coreTime inst.m inst.r inst.numEdges inst.maxMatchingCard` instructions, leaving
the maximum matching `res.mate` in `colMate[0..r)` and the closed alternating-layer distances
`res.dist` in `dist[0..m)`, while preserving `BaseRegs`, `CSRMem`, and all memory outside the
workspace `[bOff + m + 1 + numEdges, outBase)`. -/
theorem core_exec {w bOff : ℕ} (inst : SparseInstance) (x : Data 34)
    (hb : BaseRegs inst bOff x) (hcsr : CSRMem inst bOff x.mem)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    let res := hkLoop inst.graph inst.adj (inst.m + 1) 0 (Vector.replicate inst.r none)
    ∃ y, ExecWithin w coreCode x y
        (coreTime inst.m inst.r inst.numEdges inst.maxMatchingCard) ∧
      BaseRegs inst bOff y ∧
      CSRMem inst bOff y.mem ∧
      (∀ v : Fin inst.r, y.mem (bOff + inst.m + 1 + inst.numEdges + v.val) =
        match vget res.mate v with | some u => u.val | none => inst.m) ∧
      (∀ u : Fin inst.m, y.mem (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m + u.val) =
        match vget res.dist u with | none => 0 | some j => j + 1) ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
        y.mem a = x.mem a) := by
  obtain ⟨x₁, he₁, hr₁, hfill₁, hf₁⟩ := exec_fillConst bColMateReg rr rm
    (by decide) (by decide) (by decide) x hb.hone
    (by rw [hb.hbColMate, hb.hrr]; exact hfit.of_le (by omega))
    (by rw [hb.hrr]; exact hfit.of_le (by omega))
  rw [hb.hrr] at he₁ hfill₁
  rw [hb.hbColMate, hb.hrm] at hfill₁
  rw [hb.hbColMate, hb.hrr] at hf₁
  have hb₁ : BaseRegs inst bOff x₁ := hb.of_eq fun i hi => hr₁ i (by omega)
  have hs₂ : ∃ x₂, ExecWithin w (ram[ phaseActive ← one ] : Code .standard 34) x₁ x₂ 1 ∧
      x₂ = x₁.set phaseActive 1 := by
    refine WP.exists_execWithin ?_
    wram_exec [hb₁.hone]
    rfl
  obtain ⟨x₂, he₂, rfl⟩ := hs₂
  let x₂ := x₁.set phaseActive 1
  have hb₂ : BaseRegs inst bOff x₂ := hb₁.of_eq fun i hi => by dsimp only [x₂]; wram_simp
  have hcsr₂ : CSRMem inst bOff x₂.mem := hcsr.of_outside fun a ha => hf₁ a (by omega)
  have hmate₂ : MateMem inst bOff (Vector.replicate inst.r none) x₂.mem := fun v' => by
    simp only [x₂, Data.set, vget_replicate, encodeOptFin]
    exact hfill₁ v'.val v'.isLt
  have hM₀ : IsMatching inst.graph
      (mateMatching (Vector.replicate inst.r (none : Option (Fin inst.m)))) := by
    rw [mateMatching_replicate_none]
    exact ⟨by simp, by simp, by simp⟩
  have hcard₀ : (mateMatching (Vector.replicate inst.r (none : Option (Fin inst.m)))).card = 0 := by
    rw [mateMatching_replicate_none]; rfl
  obtain ⟨y, he₃, hr₃, hmate₃, hdM₃, hf₃⟩ :=
    exec_phaseLoop (inst.m + 1) 0 (Vector.replicate inst.r none) hM₀ (by omega) x₂ hb₂ hcsr₂
      hmate₂ (by dsimp only [x₂]; wram_simp) hfit
  have hph_bound :
      (hkLoop inst.graph inst.adj (inst.m + 1) 0 (Vector.replicate inst.r none)).phases ≤
        2 * Nat.sqrt inst.maxMatchingCard :=
    (hopcroftKarp_correct inst.bipAdjValid_graph).2.2.2
  have he₃' : ExecWithin w (.loop (.eq phaseActive one) phaseRoundBody) x₂ y
      (((hkLoop inst.graph inst.adj (inst.m + 1) 0
          (Vector.replicate inst.r none)).phases + 1) *
        roundTime inst.m inst.r inst.numEdges + 2) := by
    simpa only [Nat.sub_zero] using he₃
  have hmul_le :
      ((hkLoop inst.graph inst.adj (inst.m + 1) 0 (Vector.replicate inst.r none)).phases + 1) *
        roundTime inst.m inst.r inst.numEdges ≤
      (2 * Nat.sqrt inst.maxMatchingCard + 1) * roundTime inst.m inst.r inst.numEdges :=
    Nat.mul_le_mul_right _ (by omega)
  refine ⟨y, (he₁.seq (he₂.seq he₃')).mono ?_, hb₂.of_eq hr₃,
    hcsr₂.of_outside (fun a ha => hf₃ a (by omega)),
    fun v => by
      have hv := hmate₃ v
      cases h : vget (hkLoop inst.graph inst.adj (inst.m + 1) 0
          (Vector.replicate inst.r none)).mate v <;>
        simpa [encodeOptFin, h] using hv,
    fun u => by
      have hu := hdM₃ u
      cases h : vget (hkLoop inst.graph inst.adj (inst.m + 1) 0
          (Vector.replicate inst.r none)).dist u <;>
        simpa [encodeDist, h] using hu,
    fun a ha => (hf₃ a ha).trans (hf₁ a (by omega))⟩
  simp only [coreTime, roundTime] at hmul_le ⊢
  omega

/-! ## Matching output extraction (`emitMatchingCode`) -/

private def emitMatchingBody : Code .standard 34 := ram[
  addr ← bColMateReg + idx; val ← *addr;
  if val < rm then [
    val2 ← two * acc;
    addr ← outBase + one; addr ← addr + val2; *addr ← val;
    addr ← addr + one; *addr ← idx;
    acc ← acc + one
  ] else [ tmp ← zero ];
  idx ← idx + one ]

private def emitMatchingCode : Code .standard 34 :=
  .seq (ram[ acc ← #0; idx ← #0 ])
    (.seq (.loop (.lt idx rr) emitMatchingBody)
      (ram[ val2 ← two * acc; addr ← outBase; *addr ← val2 ]))

private theorem exec_emitMatchingCode {w bOff : ℕ} (inst : SparseInstance) (x : Data 34)
    (hb : BaseRegs inst bOff x)
    (hmate : ∀ v : Fin inst.r, x.mem (bOff + inst.m + 1 + inst.numEdges + v.val) =
      match vget (hkLoop inst.graph inst.adj (inst.m + 1) 0
          (Vector.replicate inst.r none)).mate v with
      | some u => u.val
      | none => inst.m)
    (hfit : Fits w (bOff + 7 * inst.m + 6 * inst.r + inst.numEdges + 8)) :
    ∃ z, ExecWithin w emitMatchingCode x z (13 * inst.r + 7) ∧
      BaseRegs inst bOff z ∧
      outputList z.mem (z.regs outBase) = inst.matchingWords ∧
      Fits w (z.regs outBase + inst.matchingWords.length) ∧
      z.regs acc = inst.maxMatchingCard := by
  let mate := (hkLoop inst.graph inst.adj (inst.m + 1) 0 (Vector.replicate inst.r none)).mate
  let mp (t : ℕ) : List (Fin inst.m × Fin inst.r) :=
    ((List.finRange inst.r).take t).filterMap fun v =>
      match vget mate v with | some u => some (u, v) | none => none
  let mw (t : ℕ) : List ℕ := (mp t).flatMap fun e => [e.1.val, e.2.val]
  let bOut := bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6
  have hmp_len : ∀ t : ℕ, (mp t).length ≤ t := fun t => by
    calc (mp t).length ≤ ((List.finRange inst.r).take t).length := List.length_filterMap_le _ _
      _ ≤ t := List.length_take_le _ _
  have hmw_len : ∀ t : ℕ, (mw t).length = 2 * (mp t).length := fun t => by
    simp [mw, List.length_flatMap, Nat.mul_comm]
  have hs₀ : ∃ s₀, ExecWithin w (ram[ acc ← #0; idx ← #0 ] : Code .standard 34) x s₀ 2 ∧
      s₀ = (x.set acc 0).set idx 0 := by
    refine WP.exists_execWithin ?_
    wram_exec
    rfl
  obtain ⟨s₀, he₀, rfl⟩ := hs₀
  let P (t : ℕ) (y : Data 34) : Prop :=
    t ≤ inst.r ∧
      (∀ i : Fin 34, i.val < 19 → y.regs i = x.regs i) ∧
      y.regs acc = (mp t).length ∧
      (∀ k : ℕ, (hk : k < (mw t).length) → y.mem (bOut + 1 + k) = (mw t)[k]'hk) ∧
      (∀ a, ¬(bOut + 1 ≤ a ∧ a < bOut + 1 + 2 * t) → y.mem a = x.mem a)
  have hP₀ : P 0 ((x.set acc 0).set idx 0) :=
    ⟨Nat.zero_le _, fun i hi => by wram_simp, by wram_simp; simp [mp],
      fun _ hk => absurd hk (by simp [mw, mp]), fun _ _ => rfl⟩
  have hbody (y : Data 34) (hy : P (y.regs idx) y) (hlt : y.regs idx < inst.r) :
      ∃ y', ExecWithin w emitMatchingBody y y' 11 ∧ P (y.regs idx + 1) y' ∧
        y'.regs idx = y.regs idx + 1 := by
    obtain ⟨_, hr, hacc_y, hblk_y, hf_y⟩ := hy
    have hby : BaseRegs inst bOff y := hb.of_eq hr
    let v : Fin inst.r := ⟨y.regs idx, hlt⟩
    have hmp_le : (mp (y.regs idx)).length ≤ y.regs idx := hmp_len (y.regs idx)
    have hcm_v : y.mem (bOff + inst.m + 1 + inst.numEdges + y.regs idx) =
        match vget mate v with | some u => u.val | none => inst.m := by
      rw [hf_y _ (by dsimp only [bOut]; omega)]
      exact hmate v
    have hmp_succ : mp (y.regs idx + 1) =
        match vget mate v with
        | some u => mp (y.regs idx) ++ [(u, v)]
        | none => mp (y.regs idx) := by
      dsimp only [mp]
      rw [List.take_succ_finRange hlt, List.filterMap_append]
      cases h : vget mate v <;> simp [v, h]
    refine WP.exists_execWithin ?_
    unfold emitMatchingBody
    cases hmv : vget mate v with
    | none =>
      rw [hmv] at hcm_v hmp_succ
      have hnl : ¬inst.m < inst.m := Nat.lt_irrefl _
      wram_exec [hby.hbColMate, hby.hrm, hby.hzero, hby.hone, hcm_v, hnl]
      refine ⟨⟨by omega, fun i hi => by wram_simp [hr i hi],
        by wram_simp [hacc_y, hmp_succ], fun k hk => ?_, fun a ha => ?_⟩, by wram_simp⟩
      · have hk' : k < (mw (y.regs idx)).length := by simpa [mw, hmp_succ] using hk
        simpa [mw, hmp_succ] using hblk_y k hk'
      · wram_simp
        exact hf_y a (by omega)
    | some u =>
      have hu_lt := u.isLt
      rw [hmv] at hcm_v hmp_succ
      have hby_ob : y.regs outBase = bOut := hby.houtBase
      wram_exec [hby.hbColMate, hby.hrm, hby.htwo, hby_ob, hby.hone, hacc_y, hcm_v, hu_lt]
      have hmw_succ : mw (y.regs idx + 1) = mw (y.regs idx) ++ [u.val, y.regs idx] := by
        dsimp only [mw]
        rw [hmp_succ, List.flatMap_append]
        rfl
      refine ⟨⟨by omega, fun i hi => by wram_simp [hr i hi],
        by wram_simp; rw [hmp_succ, List.length_append, List.length_singleton],
        fun k hk => ?_, fun a ha => ?_⟩, by wram_simp⟩
      · have hmw_l := hmw_len (y.regs idx)
        have hk_lt2 : k < 2 * (mp (y.regs idx)).length + 2 := by
          have hk' := hk
          rw [hmw_succ, List.length_append, hmw_l] at hk'
          simpa using hk'
        simp only [hmw_succ]
        by_cases hk_old : k < (mw (y.regs idx)).length
        · rw [List.getElem_append_left hk_old]
          wram_simp
          exact hblk_y k hk_old
        · rw [List.getElem_append_right (Nat.le_of_not_lt hk_old)]
          by_cases hk_eq : k = 2 * (mp (y.regs idx)).length
          · subst hk_eq
            wram_simp
            simp [hmw_l]
          · have hk_eq1 : k = 2 * (mp (y.regs idx)).length + 1 := by omega
            subst hk_eq1
            wram_simp
            simp [hmw_l]
      · wram_simp
        exact hf_y a (by omega)
  obtain ⟨y₁, hl, hPr, _⟩ := ExecWithin.loop_count P
    (fun y hy => (hy.2.1 rr (by decide)).trans hb.hrr) hbody
    (x := (x.set acc 0).set idx 0) (by simp) (by simpa using hP₀)
  obtain ⟨_, hr₁, hacc₁, hblk₁, _⟩ := hPr
  have hb₁ : BaseRegs inst bOff y₁ := hb.of_eq hr₁
  have hmp_full : mp inst.r = inst.matchingPairs := by
    dsimp only [mp, mate]
    rw [List.take_of_length_le (by simp), SparseInstance.matchingPairs_eq_mate_filterMap]
    rfl
  have hmw_full : mw inst.r = inst.matchingWords := by
    dsimp only [mw, SparseInstance.matchingWords]
    rw [hmp_full]
  have hacc_card : y₁.regs acc = inst.maxMatchingCard := by
    rw [hacc₁, hmp_full, inst.length_matchingPairs]
  have hcard_le_r : inst.maxMatchingCard ≤ inst.r := by
    rw [← inst.length_matchingPairs, ← hmp_full]
    exact hmp_len inst.r
  have hb₁_ob : y₁.regs outBase = bOut := hb₁.houtBase
  have htail : ∃ z, ExecWithin w
      (ram[ val2 ← two * acc; addr ← outBase; *addr ← val2 ] : Code .standard 34) y₁ z 3 ∧
      z = ((y₁.set val2 (2 * inst.maxMatchingCard)).set addr bOut).write
        bOut (2 * inst.maxMatchingCard) := by
    refine WP.exists_execWithin ?_
    wram_exec [hb₁.htwo, hb₁_ob, hacc_card]
    rfl
  obtain ⟨z, he_tail, rfl⟩ := htail
  let z := ((y₁.set val2 (2 * inst.maxMatchingCard)).set addr bOut).write
    bOut (2 * inst.maxMatchingCard)
  have hbz : BaseRegs inst bOff z := hb₁.of_eq fun i hi => by dsimp only [z]; wram_simp
  have hbz_ob : z.regs outBase = bOut := hbz.houtBase
  have hout_z : outputList z.mem (z.regs outBase) = inst.matchingWords := by
    rw [hbz_ob, outputList_eq_iff, inst.length_matchingWords]
    refine ⟨by dsimp only [z]; wram_simp, fun i => ?_⟩
    have hi_val : i.val < inst.matchingWords.length := i.isLt
    have hi_mw : i.val < (mw inst.r).length := by rwa [hmw_full]
    change z.mem (bOut + 1 + i.val) = inst.matchingWords[i.val]'hi_val
    have hmem_i : z.mem (bOut + 1 + i.val) = y₁.mem (bOut + 1 + i.val) := by
      dsimp only [z]
      wram_simp
    rw [hmem_i]
    simpa [hmw_full] using hblk₁ i.val hi_mw
  have hfit_out : Fits w (z.regs outBase + inst.matchingWords.length) := by
    rw [hbz_ob, inst.length_matchingWords]
    exact hfit.of_le (by omega)
  exact ⟨z, (he₀.seq (hl.seq he_tail)).mono (by simp; omega), hbz, hout_z, hfit_out,
    by dsimp only [z]; wram_simp [hacc_card]⟩

/-! ## End-to-end `State.init` sparse CSR endpoints -/

private def sparseSetupCode : Code .standard 34 :=
  .seq (ram[
    zero ← #0; one ← #1; two ← #2;
    addr ← #1; rm ← *addr;
    addr ← #2; rr ← *addr;
    bOffReg ← #3;
    addr ← bOffReg + rm; rE ← *addr ])
  initBaseRegsFromCSR

private def sparseCode : Code .standard 34 :=
  .seq sparseSetupCode (.seq coreCode emitMatchingCode)

private def checkPerfectTail : Code .standard 34 := ram[
  if rm = rr then [
    if acc = rm then [ acc ← one ] else [ acc ← zero ]
  ] else [ acc ← zero ] ]

/-- Standard-basis word-RAM program returning `inst.matchingWords` (`ExecutesList`) on a CSR
bipartite graph `inst : SparseInstance`. -/
def sparseMatchingProgram : Program .standard 34 :=
  sparseCode.program outBase

/-- Standard-basis word-RAM program returning the maximum matching cardinality
`inst.maxMatchingCard` (`Executes`) on `inst : SparseInstance`. -/
def sparseCardProgram : Program .standard 34 :=
  sparseCode.program acc

/-- Standard-basis word-RAM program deciding `SparseInstance.HasPerfectMatching` (`1` iff balanced
and admitting a perfect matching, `0` otherwise). -/
def sparsePerfectProgram : Program .standard 34 :=
  (sparseCode.seq checkPerfectTail).program acc

/-- Instruction bound `O((m + r + E) (√ν + 1))` for `sparseMatchingProgram`, `sparseCardProgram`,
and `sparsePerfectProgram`. -/
@[expose] def sparseTime (m r E ν : ℕ) : ℕ :=
  (2 * Nat.sqrt ν + 1) * (100 * m + 47 * r + 112 * E + 48) + 18 * r + 45

/-- Instance-only `O((m + r + E) √(min m r))` upper bound on `sparseTime`. -/
@[expose] def sparseTimeSqrtMin (m r E : ℕ) : ℕ :=
  sparseTime m r E (min m r)

theorem sparseTime_le_sparseTimeSqrtMin (inst : SparseInstance) :
    sparseTime inst.m inst.r inst.numEdges inst.maxMatchingCard ≤
      sparseTimeSqrtMin inst.m inst.r inst.numEdges := by
  unfold sparseTimeSqrtMin sparseTime
  have hsq : Nat.sqrt inst.maxMatchingCard ≤ Nat.sqrt (min inst.m inst.r) :=
    Nat.sqrt_le_sqrt inst.maxMatchingCard_le_min
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (by omega)) _) _

private theorem sparse_init_mem_offset {reg : ℕ} (inst : SparseInstance) {u : ℕ} (hu : u ≤ inst.m) :
    (Data.init inst.encode : Data reg).mem (3 + u) = inst.offset u := by
  have hreal := Data.init_realizes_append (r := reg) [inst.m, inst.r]
    ((List.range (inst.m + 1)).map inst.offset) inst.flatEdges
  have henc : [inst.m, inst.r] ++ (((List.range (inst.m + 1)).map inst.offset) ++ inst.flatEdges) =
      inst.encode := by simp [SparseInstance.encode]
  rw [henc] at hreal
  have h := hreal ⟨u, by simp; omega⟩
  simpa [Block.read] using h

private theorem sparse_init_mem_edge {reg : ℕ} (inst : SparseInstance) (u : Fin inst.m) {i : ℕ}
    (hi : i < (inst.adj u).length) :
    (Data.init inst.encode : Data reg).mem (inst.m + 4 + (inst.offset u.val + i)) =
      ((inst.adj u)[i]'hi).val := by
  let pre := [inst.m, inst.r] ++ (List.range (inst.m + 1)).map inst.offset
  have hreal := Data.init_realizes_append (r := reg) pre inst.flatEdges []
  have henc : pre ++ (inst.flatEdges ++ []) = inst.encode := by
    simp [pre, SparseInstance.encode]
  rw [henc] at hreal
  have hpre : pre.length + 1 = inst.m + 4 := by simp [pre]
  have hlt : inst.offset u.val + i < inst.flatEdges.length := by
    rw [inst.length_flatEdges]
    exact inst.offset_add_lt_numEdges u hi
  have h := hreal ⟨inst.offset u.val + i, hlt⟩
  change (Data.init inst.encode : Data reg).mem (pre.length + 1 + (inst.offset u.val + i)) =
    inst.flatEdges[inst.offset u.val + i] at h
  rw [hpre, SparseInstance.flatEdges_getElem inst u hi] at h
  exact h

private theorem exec_sparseCode {w : ℕ} (inst : SparseInstance) (hw : Fits w inst.wordBound) :
    ∃ z, ExecWithin w sparseCode (Data.init inst.encode) z
        (sparseTime inst.m inst.r inst.numEdges inst.maxMatchingCard - 6) ∧
      BaseRegs inst 3 z ∧
      outputList z.mem (z.regs outBase) = inst.matchingWords ∧
      Fits w (z.regs outBase + inst.matchingWords.length) ∧
      z.regs acc = inst.maxMatchingCard := by
  have hfit_all : Fits w (3 + 7 * inst.m + 6 * inst.r + inst.numEdges + 8) :=
    hw.of_le (by unfold SparseInstance.wordBound; omega)
  have hm_mem : (Data.init inst.encode : Data 34).mem 1 = inst.m := rfl
  have hr_mem : (Data.init inst.encode : Data 34).mem 2 = inst.r := rfl
  have hE_mem : (Data.init inst.encode : Data 34).mem (3 + inst.m) = inst.numEdges := by
    rw [sparse_init_mem_offset inst (le_refl inst.m), inst.offset_m]
  have hs_pre : ∃ y₀, ExecWithin w (ram[
      zero ← #0; one ← #1; two ← #2;
      addr ← #1; rm ← *addr;
      addr ← #2; rr ← *addr;
      bOffReg ← #3;
      addr ← bOffReg + rm; rE ← *addr ] : Code .standard 34) (Data.init inst.encode) y₀ 10 ∧
      y₀.regs zero = 0 ∧ y₀.regs one = 1 ∧ y₀.regs two = 2 ∧
      y₀.regs rm = inst.m ∧ y₀.regs rr = inst.r ∧ y₀.regs rE = inst.numEdges ∧
      y₀.regs bOffReg = 3 ∧ y₀.mem = (Data.init inst.encode : Data 34).mem := by
    refine WP.exists_execWithin ?_
    wram_exec [hm_mem, hr_mem, hE_mem]
    exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
      by wram_simp, by wram_simp, rfl⟩
  obtain ⟨y₀, he_pre, h0, h1, h2, hrm, hrr, hrE, hbOff, hmem₀⟩ := hs_pre
  obtain ⟨y₁, he_init, hb₁, hmem₁⟩ := exec_initBaseRegsFromCSR inst y₀ h0 h1 h2 hrm hrr hrE hbOff
    (hfit_all.of_le (by omega))
  have hcsr₁ : CSRMem inst 3 y₁.mem :=
    { hoff := fun {u} hu => by rw [hmem₁, hmem₀]; exact sparse_init_mem_offset inst hu
      hedge := fun u {i} hi => by
        rw [hmem₁, hmem₀]
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          sparse_init_mem_edge inst u hi }
  obtain ⟨y₂, he_core, hb₂, _, hmate₂, _, _⟩ := core_exec inst y₁ hb₁ hcsr₁
    (hfit_all.of_le (by omega))
  obtain ⟨z, he_emit, hbz, hout_z, hfit_out, hacc_z⟩ :=
    exec_emitMatchingCode inst y₂ hb₂ hmate₂ hfit_all
  refine ⟨z, ((he_pre.seq he_init).seq (he_core.seq he_emit)).mono ?_,
    hbz, hout_z, hfit_out, hacc_z⟩
  unfold sparseTime coreTime
  omega

/-- **`O((m + r + |E|) √ν)` Word-RAM maximum bipartite matching (`ExecutesList`).** -/
theorem executesList_sparseMatching {w : ℕ} (inst : SparseInstance) (hw : Fits w inst.wordBound) :
    ∃ steps, ExecutesList w sparseMatchingProgram (.init inst.encode) inst.matchingWords steps ∧
      steps ≤ sparseTime inst.m inst.r inst.numEdges inst.maxMatchingCard := by
  obtain ⟨z, ⟨t, ht, hex⟩, _, hout, hfit, _⟩ := exec_sparseCode inst hw
  refine ⟨t + 1, hout ▸ hex.executesList outBase (by rwa [hout]), ?_⟩
  unfold sparseTime at ht ⊢
  omega

/-- Instance-only `O((m + r + |E|) √(min m r))` corollary of `executesList_sparseMatching`. -/
theorem executesList_sparseMatching_sqrt_min {w : ℕ} (inst : SparseInstance)
    (hw : Fits w inst.wordBound) :
    ∃ steps, ExecutesList w sparseMatchingProgram (.init inst.encode) inst.matchingWords steps ∧
      steps ≤ sparseTimeSqrtMin inst.m inst.r inst.numEdges := by
  obtain ⟨steps, hex, hle⟩ := executesList_sparseMatching inst hw
  exact ⟨steps, hex, hle.trans (sparseTime_le_sparseTimeSqrtMin inst)⟩

/-- **`Program.ComputesListInTime` form of `executesList_sparseMatching`.** -/
theorem computesListInTime_sparseMatching :
    sparseMatchingProgram.ComputesListInTime (fun _ inst => inst.encode)
      (fun inst _ => sparseTime inst.m inst.r inst.numEdges inst.maxMatchingCard)
      (fun inst w => Fits w inst.wordBound) SparseInstance.matchingWords :=
  fun inst _ hw _ => executesList_sparseMatching inst hw

/-- **`O((m + r + |E|) √ν)` Word-RAM maximum matching cardinality (`Executes`).** -/
theorem executes_sparseCard {w : ℕ} (inst : SparseInstance) (hw : Fits w inst.wordBound) :
    ∃ steps, Executes w sparseCardProgram (.init inst.encode) inst.maxMatchingCard steps ∧
      steps ≤ sparseTime inst.m inst.r inst.numEdges inst.maxMatchingCard := by
  obtain ⟨z, ⟨t, ht, hex⟩, _, _, _, hacc⟩ := exec_sparseCode inst hw
  refine ⟨t + 1, hacc ▸ hex.executes acc, ?_⟩
  unfold sparseTime at ht ⊢
  omega

/-- **`Program.ComputesInTime` form of `executes_sparseCard`.** -/
theorem computesInTime_sparseCard :
    sparseCardProgram.ComputesInTime (fun _ inst => inst.encode)
      (fun inst _ => sparseTime inst.m inst.r inst.numEdges inst.maxMatchingCard)
      (fun inst w => Fits w inst.wordBound) SparseInstance.maxMatchingCard :=
  fun inst _ hw _ => executes_sparseCard inst hw

/-- **`O((m + r + |E|) √ν)` Word-RAM perfect-matching decision (`Executes`).** -/
theorem executes_sparsePerfect {w : ℕ} (inst : SparseInstance) (hw : Fits w inst.wordBound) :
    ∃ steps, Executes w sparsePerfectProgram (.init inst.encode)
        (if inst.m = inst.r ∧ inst.maxMatchingCard = inst.m then 1 else 0) steps ∧
      steps ≤ sparseTime inst.m inst.r inst.numEdges inst.maxMatchingCard := by
  obtain ⟨z, he_sp, hbz, _, _, hacc_z⟩ := exec_sparseCode inst hw
  have htail : ∃ z', ExecWithin w checkPerfectTail z z' 5 ∧
      z'.regs acc = if inst.m = inst.r ∧ inst.maxMatchingCard = inst.m then 1 else 0 := by
    refine WP.exists_execWithin ?_
    unfold checkPerfectTail
    by_cases hmr : inst.m = inst.r
    · by_cases hcm : inst.maxMatchingCard = inst.m
      · wram_exec [hbz.hrm, hbz.hrr, hbz.hone, hacc_z, hmr, hcm]
        wram_simp; simp [hmr, hcm]
      · wram_exec [hbz.hrm, hbz.hrr, hbz.hzero, hacc_z, hmr, hcm]
        wram_simp; simp [hcm]
    · wram_exec [hbz.hrm, hbz.hrr, hbz.hzero, hmr]
      wram_simp; simp [hmr]
  obtain ⟨z', he_t, hacc'⟩ := htail
  obtain ⟨t, ht, hex⟩ := he_sp.seq he_t
  refine ⟨t + 1, hacc' ▸ hex.executes acc, ?_⟩
  unfold sparseTime at ht ⊢
  omega

/-- **`Program.DecidesInTime` form of `executes_sparsePerfect`.** -/
theorem decidesInTime_sparsePerfect :
    sparsePerfectProgram.DecidesInTime (fun _ (inst : SparseInstance) => inst.encode)
      {inst | inst.HasPerfectMatching}
      (fun inst _ => sparseTime inst.m inst.r inst.numEdges inst.maxMatchingCard)
      (fun inst w => Fits w inst.wordBound) := by
  intro inst w hw _
  obtain ⟨steps, hex, hle⟩ := executes_sparsePerfect inst hw
  refine ⟨_, steps, hex, hle, by split_ifs <;> omega, ?_⟩
  change _ ↔ inst.HasPerfectMatching
  rw [inst.hasPerfectMatching_iff]
  split_ifs with h <;> simp [h]

/-! ## End-to-end `State.init` dense endpoints -/

private def denseCode : Code .standard 34 :=
  .seq (matrixSetupCode false) (.seq coreCode emitMatchingCode)

/-- Standard-basis word-RAM program returning `inst.matchingWords` (`ExecutesList`) on a dense
`m × r` `0/1` adjacency matrix `inst : DenseInstance`. -/
def denseMatchingProgram : Program .standard 34 :=
  denseCode.program outBase

/-- Standard-basis word-RAM program returning `inst.maxMatchingCard` (`Executes`) on
`inst : DenseInstance`. -/
def denseCardProgram : Program .standard 34 :=
  denseCode.program acc

/-- Instruction bound `O((m + r)² √ν)` for `denseMatchingProgram` and `denseCardProgram`. -/
@[expose] def denseTime (m r ν : ℕ) : ℕ :=
  (2 * Nat.sqrt ν + 1) * (112 * m * r + 100 * m + 47 * r + 48) +
    9 * m * r + 8 * m + 18 * r + 50

private theorem dense_init_mem_entry {reg : ℕ} (inst : DenseInstance) (u : Fin inst.m)
    (v : Fin inst.r) :
    (Data.init inst.encode : Data reg).mem (3 + (u.val * inst.r + v.val)) =
      if inst.graph (u, v) then 1 else 0 := by
  let g : Fin inst.m → List ℕ := fun u' =>
    (List.finRange inst.r).map fun v' => if inst.graph (u', v') then 1 else 0
  have h := List.getElem?_flatMap_mul_add (List.finRange inst.m) g inst.r
    (fun _ _ => by simp [g]) (show u.val < (List.finRange inst.m).length by simp) v.isLt
  rw [show 3 + (u.val * inst.r + v.val) = (u.val * inst.r + v.val) + 1 + 1 + 1 by omega,
    Data.init_mem_succ, DenseInstance.encode, List.getD_cons_succ, List.getD_cons_succ,
    List.getD_eq_getElem?_getD, h]
  simp [g]

private theorem exec_denseCode {w : ℕ} (inst : DenseInstance) (hw : Fits w inst.wordBound) :
    ∃ z, ExecWithin w denseCode (Data.init inst.encode) z
        (denseTime inst.m inst.r inst.maxMatchingCard - 1) ∧
      outputList z.mem (z.regs outBase) = inst.matchingWords ∧
      Fits w (z.regs outBase + inst.matchingWords.length) ∧
      z.regs acc = inst.maxMatchingCard := by
  have hfit_all : Fits w ((3 + inst.m * inst.r) + 7 * inst.m + 6 * inst.r +
      inst.m * inst.r + 8) := hw.of_le (by unfold DenseInstance.wordBound; nlinarith)
  obtain ⟨y₁, he_setup, hb₁, hcsr₁⟩ :=
    exec_matrixSetupCode (m := inst.m) (r := inst.r) false (fun h => by cases h)
      inst.graph inst.encode rfl (fun _ => rfl)
      (fun u v => dense_init_mem_entry inst u v) (hfit_all.of_le (by simp; omega))
  have hE_le : inst.toSparse.numEdges ≤ inst.m * inst.r := inst.numEdges_toSparse_le
  have hfit_core : Fits w ((3 + inst.m * inst.r) + 7 * inst.toSparse.m + 5 * inst.toSparse.r +
      inst.toSparse.numEdges + 8) := by
    change Fits w ((3 + inst.m * inst.r) + 7 * inst.m + 5 * inst.r +
      inst.toSparse.numEdges + 8)
    exact hfit_all.of_le (by omega)
  have hfit_emit : Fits w ((3 + inst.m * inst.r) + 7 * inst.toSparse.m + 6 * inst.toSparse.r +
      inst.toSparse.numEdges + 8) := by
    change Fits w ((3 + inst.m * inst.r) + 7 * inst.m + 6 * inst.r +
      inst.toSparse.numEdges + 8)
    exact hfit_all.of_le (by omega)
  obtain ⟨y₂, he_core, hb₂, _, hmate₂, _, _⟩ := core_exec inst.toSparse y₁ hb₁ hcsr₁ hfit_core
  obtain ⟨z, he_emit, _, hout_z, hfit_out, hacc_z⟩ :=
    exec_emitMatchingCode inst.toSparse y₂ hb₂ hmate₂ hfit_emit
  rw [← inst.maxMatchingCard_eq_toSparse] at he_core hacc_z
  have hcore_le : coreTime inst.m inst.r inst.toSparse.numEdges inst.maxMatchingCard ≤
      (2 * Nat.sqrt inst.maxMatchingCard + 1) *
        (112 * inst.m * inst.r + 100 * inst.m + 47 * inst.r + 48) + 5 * inst.r + 6 := by
    unfold coreTime
    refine Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) _) _
    nlinarith
  refine ⟨z, (he_setup.seq (he_core.seq he_emit)).mono ?_,
    hout_z, hfit_out, hacc_z⟩
  unfold denseTime
  change (9 * inst.m * inst.r + 8 * inst.m + 35) +
      (coreTime inst.m inst.r inst.toSparse.numEdges inst.maxMatchingCard +
        (13 * inst.r + 7)) ≤ _
  omega

/-- **`O((m + r)² √ν)` Word-RAM dense maximum bipartite matching (`ExecutesList`).** -/
theorem executesList_denseMatching {w : ℕ} (inst : DenseInstance) (hw : Fits w inst.wordBound) :
    ∃ steps, ExecutesList w denseMatchingProgram (.init inst.encode) inst.matchingWords steps ∧
      steps ≤ denseTime inst.m inst.r inst.maxMatchingCard := by
  obtain ⟨z, ⟨t, ht, hex⟩, hout, hfit, _⟩ := exec_denseCode inst hw
  refine ⟨t + 1, hout ▸ hex.executesList outBase (by rwa [hout]), ?_⟩
  unfold denseTime at ht ⊢
  omega

/-- **`Program.ComputesListInTime` form of `executesList_denseMatching`.** -/
theorem computesListInTime_denseMatching :
    denseMatchingProgram.ComputesListInTime (fun _ inst => inst.encode)
      (fun inst _ => denseTime inst.m inst.r inst.maxMatchingCard)
      (fun inst w => Fits w inst.wordBound) DenseInstance.matchingWords :=
  fun inst _ hw _ => executesList_denseMatching inst hw

/-- **`O((m + r)² √ν)` Word-RAM dense maximum matching cardinality (`Executes`).** -/
theorem executes_denseCard {w : ℕ} (inst : DenseInstance) (hw : Fits w inst.wordBound) :
    ∃ steps, Executes w denseCardProgram (.init inst.encode) inst.maxMatchingCard steps ∧
      steps ≤ denseTime inst.m inst.r inst.maxMatchingCard := by
  obtain ⟨z, ⟨t, ht, hex⟩, _, _, hacc⟩ := exec_denseCode inst hw
  refine ⟨t + 1, hacc ▸ hex.executes acc, ?_⟩
  unfold denseTime at ht ⊢
  omega

/-- **`Program.ComputesInTime` form of `executes_denseCard`.** -/
theorem computesInTime_denseCard :
    denseCardProgram.ComputesInTime (fun _ inst => inst.encode)
      (fun inst _ => denseTime inst.m inst.r inst.maxMatchingCard)
      (fun inst w => Fits w inst.wordBound) DenseInstance.maxMatchingCard :=
  fun inst _ hw _ => executes_denseCard inst hw

end Cslib.Algorithms.WordRAM.HopcroftKarp
