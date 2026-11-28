/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.Phase
public import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.FinCases

/-!
# Worked Tests for `Algorithms.WordRAM.MinimumSpanningForest.DenseCase` (`Layout`, `Scan`, `Phase`)

Exercises:
1. `computeThreshProg`: boundary (`n = 1, mRef = 0`), clamped (`n = 3, mRef = 10`), and unclamped
   (`n = 10, mRef = 5`) pure-register threshold evaluations with `memoryCost = 0`.
2. `ftPhaseProg` (`ftPhaseProg_spec`): 1-vertex empty graph and 3-vertex weighted simple triangle
   with explicit `HoldsIndexedEdges` and `HoldsUndirCSR` layouts, plus width-blind
   `Program .standard` lowering via `realizes_ftPhaseProg`.
3. `ftRunTree` (`ftRunTree_spec`): 2-vertex single-edge tree growth, sparse Fibonacci heap reset,
   `FTPhaseInv` advancement, and amortized potential accounting.
4. `ftPhaseRank` and `ftPhase_rank_lt_of_shrink`: concrete 10-vertex bipartite contraction proving
   strict phase-rank decrease, plus `nCur = 0` boundary.
5. `csrAndPhaseProg`: `buildUndirCSR >>= ftPhaseProg` `realize` composition over a multigraph with
   a self-loop, parallel edges (`decreaseKey` and skip paths), duplicate weights, isolated vertex,
   and bounded-heap overflow (`ctx.thresh = 1 < sz`).
-/

public section

namespace CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.DenseCasePhase

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.PriorityQueue Cslib.DataStructure.PriorityQueue.FibonacciHeap
open Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native
open Cslib.Algorithms.Lean.Kruskal Cslib.Algorithms.WordRAM.MinimumSpanningForest
open Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase
open Cslib.Query.MinimumSpanningForest

/-! ## 1. Pure-register `computeThreshProg` tests -/

/-- Pure-register `computeThreshProg` handles `n = 1, mRef = 0`, clamped `n = 3, mRef = 10`, and
unclamped `n = 10, mRef = 5` with `s' = s` and `memoryCost = 0`. -/
theorem computeThreshProg_cases (s : Memory.State) :
    (Memory.spec 0).clientResult s (computeThreshProg 1 0) = 1 ∧
    (Memory.spec 0).clientState s (computeThreshProg 1 0) = s ∧
    memoryCost (computeThreshProg 1 0) s = 0 ∧
    (Memory.spec 0).clientResult s (computeThreshProg 3 10) = 3 ∧
    memoryCost (computeThreshProg 3 10) s = 0 ∧
    (Memory.spec 0).clientResult s (computeThreshProg 10 5) = 2 ∧
    memoryCost (computeThreshProg 10 5) s = 0 := by
  obtain ⟨_, _, hs1, hr1, _, _, hc1⟩ :=
    computeThreshProg_spec (w := 16) (n := 1) (mRef := 0) (s := s)
      (by decide) (by decide) (by decide)
  obtain ⟨_, _, _, hr2, _, _, hc2⟩ :=
    computeThreshProg_spec (w := 16) (n := 3) (mRef := 10) (s := s)
      (by decide) (by decide) (by decide)
  obtain ⟨_, _, _, hr3, _, _, hc3⟩ :=
    computeThreshProg_spec (w := 16) (n := 10) (mRef := 5) (s := s)
      (by decide) (by decide) (by decide)
  norm_num at hr1 hr2 hr3
  exact ⟨hr1, hs1, hc1, hr2, hc2, hr3, hc3⟩

/-! ## 2. 1-vertex empty-graph phase and `Program .standard` lowering -/

/-- Input word list for `ftPhaseProg` on `n = 1, m = 0, mRef = 2`, with `off = [0, 0]` at
addresses `8, 9`, `selBufBase = 10`, and `frontier = 12`. -/
@[expose] def oneVertWords : List ℕ :=
  [1, 0, 2, 10, 8, 10, 10, 0, 0, 0, 0]

/-- Arguments encoded in `oneVertWords`. -/
@[expose] def oneVertArgs : FTPhaseArgs :=
  ⟨1, 0, 2, 10, 8, 10, 10, 0⟩

private theorem oneVert_spec_facts :
    let s := Memory.State.init oneVertWords
    let prog := ftPhaseProg oneVertArgs
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    ftPhaseProgSafe 16 oneVertArgs s ∧
    (Memory.spec 16).ValidHistory s ((Memory.spec 16).clientHistory s prog) ∧
    s'.frontier = 31 ∧
    res.nComp = 1 ∧ res.compBase + 1 ≤ 31 ∧ res.selLen = 0 ∧
    s'.mem res.compBase = 0 ∧
    memoryCost prog s ≤ 531 := by
  let s := Memory.State.init oneVertWords
  have hwf : Memory.WellFormed 16 s := Memory.wellFormed_init (by decide) (by decide)
  have hin : HoldsIndexedEdges (n := 1) 10 [] s.mem := fun _ hi => by simp at hi
  have hcsr : HoldsUndirCSR (n := 1) 8 10 [] s.mem := by
    refine ⟨rfl, fun u => by fin_cases u; decide, by decide, fun u => ?_⟩
    fin_cases u; decide
  have hsp := ftPhaseProg_spec (w := 16) (n := 1) (mRef := 2) (es := [])
    (edgeBase := 10) (offBase := 8) (adjBase := 10) (selBufBase := 10) (selLen0 := 0) (s := s)
    (by decide) hwf (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (.inr (by decide)) (.inr (by decide)) (.inr (by decide)) hin hcsr
  dsimp only at hsp
  have hargs :
      (⟨1, ([] : List (IndexedEdge 1)).length, 2, 10, 8, 10, 10, 0⟩ : FTPhaseArgs) = oneVertArgs :=
    rfl
  rw [hargs] at hsp
  rcases hsp with ⟨hsafe, hv, hfr, _, _, hcb, hnc1, hnc_le,
    ⟨selEs, compFn, hsub, hselLen, _, _, _, _, _, hcomp_mem, _, _⟩, hcost⟩
  have hnc_eq : ((Memory.spec 0).clientResult s (ftPhaseProg oneVertArgs)).nComp = 1 := by
    omega
  have hsel_nil : selEs = [] := by
    have := hsub.length_le
    simp only [List.length_nil] at this
    exact List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero this)
  have hsel_eq : ((Memory.spec 0).clientResult s (ftPhaseProg oneVertArgs)).selLen = 0 := by
    rw [hselLen, hsel_nil]; rfl
  have hfr_eq : ((Memory.spec 0).clientState s (ftPhaseProg oneVertArgs)).frontier = 31 := by
    rw [hfr]; decide
  have hcomp0 : ((Memory.spec 0).clientState s (ftPhaseProg oneVertArgs)).mem
      ((Memory.spec 0).clientResult s (ftPhaseProg oneVertArgs)).compBase = 0 := by
    have hu := hcomp_mem (0 : Fin 1)
    simp only [Fin.val_zero, Nat.add_zero] at hu
    rw [hu]
    have hlt := (compFn 0).isLt
    omega
  refine ⟨hsafe, hv, hfr_eq, hnc_eq, ?_, hsel_eq, hcomp0, ?_⟩
  · simpa only [hfr_eq] using hcb
  · simp only [List.length_nil] at hcost; omega

/-- Lowering `realizes_ftPhaseProg` via `exists_standard_basis_init_program_state_from_words`
yields a deterministic width-blind `Program .standard` halting with `nComp = 1`, `selLen = 0`,
and `frontier = 31`. -/
theorem exists_standard_ftPhaseProg_oneVertex_halts :
    ∃ r C pc : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
      ∃ frontier : Fin r, ∃ out : Fin 3 → Fin r, ∃ y n,
        Runs 16 prog (State.init oneVertWords) ⟨pc, y⟩ n ∧
        step 16 prog ⟨pc, y⟩ = .halt 1 ∧
        y.regs (out 2) = 0 ∧
        (memoryState frontier y).frontier = 31 ∧
        n + 1 ≤ C * (memoryCost (ftPhaseProg oneVertArgs) (Memory.State.init oneVertWords) +
          ((2 * oneVertArgs.mRef) / oneVertArgs.n + 2) + 1) + 1 := by
  obtain ⟨r, C, pc, prog, hnw, frontier, out, hrun⟩ :=
    realizes_ftPhaseProg.exists_standard_basis_init_program_state_from_words (0 : Fin 3)
  have hprog_rf : (stripRand prog).IsRandFree := isRandFree_stripRand prog
  have hprog_nw : ¬(stripRand prog).ReadsWidth := not_readsWidth_stripRand hnw
  have hlayout :
      ∀ j : Fin 8, oneVertWords.getD j.val 0 = WordEncoding.encode oneVertArgs j := by
    intro j; fin_cases j <;> rfl
  obtain ⟨hsafe, hv, hfr, hnc, _, hsel, _, _⟩ := oneVert_spec_facts
  obtain ⟨y, n, hruns, hhalt, hmem_eq, hregs, hsteps⟩ :=
    hrun 16 oneVertArgs oneVertWords hlayout (by decide) (by decide) (by decide) hsafe hv
  have hres_w := clientResult_width (p := ftPhaseProg oneVertArgs)
    (s := Memory.State.init oneVertWords) 16
  have hst_w := clientState_width (p := ftPhaseProg oneVertArgs)
    (s := Memory.State.init oneVertWords) 16
  have h0 : WordEncoding.encode ((Memory.spec 0).clientResult
      (Memory.State.init oneVertWords) (ftPhaseProg oneVertArgs)) (0 : Fin 3) = 1 := hnc
  have hhalt' : step 16 prog ⟨pc, y⟩ = .halt 1 := by
    rw [hhalt, hres_w, h0]
  have hreg2 : y.regs (out 2) = 0 := by
    rw [hregs 2, hres_w]
    change ((Memory.spec 0).clientResult (Memory.State.init oneVertWords)
      (ftPhaseProg oneVertArgs)).selLen = 0
    exact hsel
  have hfr' : (memoryState frontier y).frontier = 31 := by
    rw [hmem_eq, hst_w]; exact hfr
  exact ⟨r, C, pc, stripRand prog, hprog_nw, hprog_rf, frontier, out, y, n,
    runs_stripRand hruns, step_stripRand_of_halt hhalt', hreg2, hfr', hsteps⟩

/-! ## 3. Concrete 3-vertex weighted triangle phase test -/

/-- Three-vertex weighted simple triangle `[(0, 1, 2, 10), (1, 2, 3, 11), (0, 2, 5, 12)]`. -/
@[expose] def triEs : List (IndexedEdge 3) :=
  [⟨0, 1, 2, 10⟩, ⟨1, 2, 3, 11⟩, ⟨0, 2, 5, 12⟩]

/-- Memory table for `triEs` under `Memory.State.init` (`mem (a + 1) = triWords[a]`):
* `[1..13)`: stride-4 `IndexedEdge` entries at `edgeBase = 1`,
* `[13..17)`: CSR offsets `[0, 2, 4, 6]` at `offBase = 13`,
* `[17..29)`: undirected CSR pairs `[(1,0), (2,2), (0,0), (2,1), (0,2), (1,1)]` at `adjBase = 17`,
* `[29..32)`: reserved `selBufBase = 29`, with `frontier = 32`. -/
@[expose] def triWords : List ℕ :=
  [ 0, 1, 2, 10,  1, 2, 3, 11,  0, 2, 5, 12,
    0, 2, 4, 6,
    1, 0, 2, 2,  0, 0, 2, 1,  0, 2, 1, 1,
    0, 0, 0 ]

/-- `ftPhaseProg` produces an acyclic, MSF-extending contraction on the 3-vertex simple triangle
within cost `≤ 234 * 3 + 156 * 3 + 184 * 3 + 7`. -/
theorem ftPhaseProg_triangle_spec :
    let s := Memory.State.init triWords
    let args : FTPhaseArgs := ⟨3, 3, 3, 1, 13, 17, 29, 0⟩
    let prog := ftPhaseProg args
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = 79 ∧
    1 ≤ res.nComp ∧ res.nComp ≤ 3 ∧
    (∃ (selEs : List (IndexedEdge 3)) (compFn : Fin 3 → Fin res.nComp),
      selEs.Subperm triEs ∧
      res.selLen = selEs.length ∧
      selEs.length + res.nComp = 3 ∧
      (∀ j (hj : j < selEs.length), s'.mem (29 + j) = selEs[j].id) ∧
      IsAcyclic (selEs.map IndexedEdge.toWeighted) ∧
      (∃ F_ext : List (WeightedEdge 3 ℕ),
        IsMinSpanningForest (triEs.map IndexedEdge.toWeighted)
          (selEs.map IndexedEdge.toWeighted ++ F_ext)) ∧
      Function.Surjective compFn ∧
      (∀ u : Fin 3, s'.mem (res.compBase + u.val) = (compFn u).val)) ∧
    memoryCost prog s ≤ 1729 := by
  let s := Memory.State.init triWords
  have hwf : Memory.WellFormed 16 s := Memory.wellFormed_init (by decide) (by decide)
  have hin : HoldsIndexedEdges 1 triEs s.mem := fun i hi => by
    simp only [triEs, List.length_cons, List.length_nil] at hi
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi' with rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl⟩
  have hcsr : HoldsUndirCSR 13 17 triEs s.mem := by
    refine ⟨rfl, fun u => by fin_cases u <;> decide, by decide, fun u => ?_⟩
    fin_cases u <;> decide
  have hsp := ftPhaseProg_spec (w := 16) (n := 3) (mRef := 3) (es := triEs)
    (edgeBase := 1) (offBase := 13) (adjBase := 17) (selBufBase := 29) (selLen0 := 0) (s := s)
    (by decide) hwf (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (.inr (by decide)) (.inr (by decide)) (.inr (by decide)) hin hcsr
  dsimp only at hsp
  rw [show (⟨3, triEs.length, 3, 1, 13, 17, 29, 0⟩ : FTPhaseArgs) =
      ⟨3, 3, 3, 1, 13, 17, 29, 0⟩ from rfl] at hsp
  rcases hsp with ⟨_, _, hfr, _, _, _, hnc1, hnc_le,
    ⟨selEs, compFn, hsub, hselLen, hcard, hbuf, hac, hext, hsurj, hcomp_mem, _, _⟩, hcost⟩
  have hfr' : ((Memory.spec 0).clientState s
      (ftPhaseProg ⟨3, 3, 3, 1, 13, 17, 29, 0⟩)).frontier = 79 := by
    rw [hfr]; decide
  refine ⟨hfr', hnc1, hnc_le, ⟨selEs, compFn, hsub, ?_, hcard, ?_, hac, hext, hsurj, hcomp_mem⟩,
    by simpa only [triEs, List.length_cons, List.length_nil] using hcost⟩
  · simpa only [Nat.zero_add] using hselLen
  · intro j hj; simpa only [Nat.add_zero] using hbuf j hj

/-! ## 4. Direct `ftRunTree` test on a 2-vertex single-edge graph -/

/-- Two-vertex single-edge graph `[(0, 1, 7, 42)]`. -/
@[expose] def twoVertEs : List (IndexedEdge 2) :=
  [⟨0, 1, 7, 42⟩]

/-- Memory image for `ftRunTree` on `twoVertEs`:
* `[0..4)`: `⟨0, 1, 7, 42⟩` at `edgeBase = 0`,
* `[4..7)`: CSR offsets `[0, 1, 2]` at `offBase = 4`,
* `[7..11)`: CSR adjacency `[(1, 0), (0, 0)]` at `adjBase = 7`,
* `[11..13)`: `selBufBase = 11`,
* `[13..36)`: zero-cleared Fibonacci heap block of size `9 * 2 + 5 = 23` via `allocProg 2`,
* `[36..46)`: `5 * 2 = 10`-word scratch `aux` with `tr = [2, 2]` at `[36, 37]`, `frontier = 46`. -/
@[expose] def twoVertInit : Memory.State :=
  ⟨fun a =>
    if a = 1 then 1
    else if a = 2 then 7
    else if a = 3 then 42
    else if a = 5 then 1
    else if a = 6 then 2
    else if a = 7 then 1
    else if a = 36 then 2
    else if a = 37 then 2
    else 0, 46⟩

private theorem twoVertInit_wf : Memory.WellFormed 16 twoVertInit :=
  { frontier_fits := by decide
    mem_fits := fun a => by dsimp only [twoVertInit]; split_ifs <;> decide }

/-- Single-tree `ftRunTree_spec` execution on `twoVertEs` grows the tree from `t = 0`, resets the
Fibonacci heap back to empty with `potential = 0`, advances `FTPhaseInv`, and respects the
amortized potential inequality `cost + pot' ≤ 7 + pot`. -/
theorem ftRunTree_twoVertex_spec :
    let ctx : FTCtx := ⟨2, 1, 0, 4, 7, 13, 36, 11, 2⟩
    let prog := ftRunTree ⟨ctx, 0, 0, 0⟩
    let res := (Memory.spec 0).clientResult (⟨clear twoVertInit.mem 13 23, 46⟩ : Memory.State)
      prog
    let s' := (Memory.spec 0).clientState (⟨clear twoVertInit.mem 13 23, 46⟩ : Memory.State)
      prog
    s'.frontier = 46 ∧
    potential 2 ((layout 2 13).abs s') = 0 ∧
    (∃ selIdxs', FTPhaseInv ctx twoVertEs 1 res.1 0 res.2 selIdxs' s'.mem) ∧
    memoryCost prog ⟨clear twoVertInit.mem 13 23, 46⟩ +
      (∑ v : Fin 2,
        if s'.mem (36 + v.val) < 1 then 0 else vertexPot ctx 2 1 v s'.mem) ≤
      7 +
      (∑ v : Fin 2,
        if clear twoVertInit.mem 13 23 (36 + v.val) < 0 then 0
        else vertexPot ctx 2 1 v (clear twoVertInit.mem 13 23)) := by
  have hn : Fits 16 2 := by decide
  have hK : Fits 16 7 := by decide
  let sBase : Memory.State := ⟨twoVertInit.mem, 13⟩
  have hwfBase : Memory.WellFormed 16 sBase :=
    { frontier_fits := by decide
      mem_fits := twoVertInit_wf.mem_fits }
  have hfh := allocProg_spec hwfBase hn hK (by decide)
  dsimp only at hfh
  rcases hfh with ⟨_, _, _, hwfClear, _, hinvClear, hempClear, hpotClear, _⟩
  let s0 : Memory.State := ⟨clear twoVertInit.mem 13 23, 46⟩
  have hsClear_eq : (Memory.spec 0).clientState sBase (allocProg 2) =
      ⟨clear twoVertInit.mem 13 23, 36⟩ := rfl
  rw [hsClear_eq] at hwfClear hinvClear hempClear hpotClear
  have hwf0 : Memory.WellFormed 16 s0 :=
    { frontier_fits := by decide
      mem_fits := hwfClear.mem_fits }
  obtain ⟨hinv0, habs0, hpot0⟩ := framed_preserved (s' := s0) hinvClear (fun _ _ => rfl)
    (by decide) (by decide)
  have hclr_ne : ∀ a, a < 13 ∨ 36 ≤ a → s0.mem a = twoVertInit.mem a := fun a ha => by
    dsimp only [s0]
    exact clear_of_not_owns (show ¬Block.Owns ⟨13, 23⟩ a by simp [Block.Owns]; omega)
  let ctx : FTCtx := ⟨2, 1, 0, 4, 7, 13, 36, 11, 2⟩
  have hin0 : HoldsIndexedEdges 0 twoVertEs s0.mem := fun i hi => by
    have : i = 0 := by simp only [twoVertEs, List.length_cons, List.length_nil] at hi; omega
    subst this
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (rw [hclr_ne _ (Or.inl (by decide))]; rfl)
  have hcsr0 : HoldsUndirCSR 4 7 twoVertEs s0.mem :=
    HoldsUndirCSR.congr (fun a _ ha => hclr_ne a (Or.inl (by omega)))
      (fun a _ ha => hclr_ne a (Or.inl (by
        simp only [twoVertEs, List.length_cons, List.length_nil] at ha; omega)))
      ⟨rfl, fun u => by fin_cases u <;> decide, rfl, fun u => by fin_cases u <;> decide⟩
  let hs : FTStatic 16 2 7 1 0 ctx twoVertEs s0 :=
    { fit16 := by decide
      cn := rfl
      cm := rfl
      hn := hn
      hK := hK
      fitFh := by decide
      fitAux := by decide
      fitOff := by decide
      fitAdj := by decide
      fitEdge := by decide
      fit2m := by decide
      fitSel := by decide
      offFr := by decide
      adjFr := by decide
      edgeFr := by decide
      auxFr := by decide
      selFr := by decide
      fhLtAux := by decide
      edgeLtFh := by decide
      offLtFh := by decide
      adjLtFh := by decide
      selDisjFh := Or.inl (by decide)
      selDisjAux := Or.inl (by decide)
      selDisjEdge := Or.inr (by decide)
      selDisjOff := Or.inr (by decide)
      selDisjAdj := Or.inr (by decide)
      hin := hin0
      hcsr := hcsr0
      hKes := fun e he => by simp only [twoVertEs, List.mem_singleton] at he; subst he; decide
      threshLe := by decide }
  have hvis0 : visitedSet 36 2 0 s0.mem = ∅ := by
    ext v; simp only [mem_visitedSet, Finset.notMem_empty, iff_false]; omega
  have hphase0 : FTPhaseInv ctx twoVertEs 0 0 0 (0 + ([] : List (Fin twoVertEs.length)).length)
      [] s0.mem :=
    ⟨fun v => Or.inr (by
        fin_cases v <;> rw [hclr_ne _ (Or.inr (by decide))] <;> decide),
      fun _ hv => absurd hv (by omega), le_rfl, rfl, by rw [hvis0]; simp, List.nodup_nil,
      fun _ h => by simp at h, by simp [isAcyclic_nil],
      exists_extend_isMinSpanningForest_of_subperm_msfEdges
        (twoVertEs.map IndexedEdge.toWeighted) [] List.nil_subperm,
      fun _ hj => by simp at hj, fun _ hv => by rw [hvis0] at hv; simp at hv,
      fun _ hx => by rw [hvis0] at hx; simp at hx, fun c => absurd c.isLt (by omega)⟩
  have ht_tr_n : s0.mem (36 + (0 : Fin 2).val) = 2 := by
    simp only [Fin.val_zero, Nat.add_zero]
    rw [hclr_ne 36 (Or.inr (by decide))]; rfl
  have hrt := ftRunTree_spec hs hwf0 ht_tr_n hinv0 (habs0.trans hempClear)
    (hpot0.trans hpotClear) hphase0
  dsimp only at hrt
  rcases hrt with ⟨_, _, hfr', _, _, _, _, hpot', ⟨sel', hph'⟩, hcost'⟩
  exact ⟨hfr', hpot', ⟨sel', by simpa using hph'⟩, hcost'⟩

/-! ## 5. `ftPhaseRank` and strict phase-rank decrease test -/

/-- Concrete 10-vertex, 9-edge bipartite graph witnessing `ftPhase_rank_lt_of_shrink` from
`n = 10` (`mRef = 10`, threshold `4`) down to `nOut = 2`. -/
@[expose] def bipEs : List (IndexedEdge 10) :=
  [ ⟨0, 5, 1, 0⟩, ⟨0, 6, 1, 1⟩, ⟨0, 7, 1, 2⟩, ⟨0, 8, 1, 3⟩, ⟨0, 9, 1, 4⟩,
    ⟨1, 5, 1, 5⟩, ⟨2, 5, 1, 6⟩, ⟨3, 5, 1, 7⟩, ⟨4, 5, 1, 8⟩ ]

/-- Component map collapsing `{0..4}` to `0` and `{5..9}` to `1`. -/
@[expose] def bipComp (u : Fin 10) : Fin 2 :=
  ⟨if u.val < 5 then 0 else 1, by split_ifs <;> omega⟩

/-- Concrete contraction shrinks `ftPhaseRank 10 10` strictly to `ftPhaseRank 10 2`, and
`ftPhaseRank 10 0 = 0`. -/
theorem ftPhaseRank_shrink_and_zero :
    ftPhaseRank 10 0 = 0 ∧
    ftPhaseRank 10 2 < ftPhaseRank 10 10 := by
  have hzero : ftPhaseRank 10 0 = 0 := rfl
  let esCon : List (IndexedEdge 2) :=
    bipEs.map (fun e => ⟨bipComp e.u, bipComp e.v, e.weight, e.id⟩)
  let esDedup : List (IndexedEdge 2) := [⟨0, 1, 1, 0⟩]
  have hdedup_sub : esDedup.Subperm esCon :=
    (List.singleton_sublist.mpr (by simp [esCon, bipEs, bipComp])).subperm
  have hdeg : ∀ c : Fin 2,
      (∀ e ∈ bipEs, bipComp e.u = c ↔ bipComp e.v = c) ∨
      ∃ A Z : Finset (Fin 10),
        (∀ u ∈ A, bipComp u = c) ∧
        min 10 (2 ^ ((2 * 10) / 10)) + 1 ≤ Z.card ∧
        ∀ z ∈ Z, z ∉ A ∧ ∃ e ∈ bipEs, (e.u ∈ A ∧ e.v = z) ∨ (e.v ∈ A ∧ e.u = z) := by
    intro c
    right
    fin_cases c
    · refine ⟨{0, 1, 2, 3, 4}, {5, 6, 7, 8, 9}, ?_, by decide, ?_⟩
      · intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl | rfl | rfl <;> decide
      · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl
        all_goals refine ⟨by decide, ?_⟩
        · exact ⟨⟨0, 5, 1, 0⟩, by simp [bipEs], .inl ⟨by decide, rfl⟩⟩
        · exact ⟨⟨0, 6, 1, 1⟩, by simp [bipEs], .inl ⟨by decide, rfl⟩⟩
        · exact ⟨⟨0, 7, 1, 2⟩, by simp [bipEs], .inl ⟨by decide, rfl⟩⟩
        · exact ⟨⟨0, 8, 1, 3⟩, by simp [bipEs], .inl ⟨by decide, rfl⟩⟩
        · exact ⟨⟨0, 9, 1, 4⟩, by simp [bipEs], .inl ⟨by decide, rfl⟩⟩
    · refine ⟨{5, 6, 7, 8, 9}, {0, 1, 2, 3, 4}, ?_, by decide, ?_⟩
      · intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl | rfl | rfl <;> decide
      · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl
        all_goals refine ⟨by decide, ?_⟩
        · exact ⟨⟨0, 5, 1, 0⟩, by simp [bipEs], .inr ⟨by decide, rfl⟩⟩
        · exact ⟨⟨1, 5, 1, 5⟩, by simp [bipEs], .inr ⟨by decide, rfl⟩⟩
        · exact ⟨⟨2, 5, 1, 6⟩, by simp [bipEs], .inr ⟨by decide, rfl⟩⟩
        · exact ⟨⟨3, 5, 1, 7⟩, by simp [bipEs], .inr ⟨by decide, rfl⟩⟩
        · exact ⟨⟨4, 5, 1, 8⟩, by simp [bipEs], .inr ⟨by decide, rfl⟩⟩
  have hlt := (ftPhase_rank_lt_of_shrink (n := 10) (nComp := 2) (nOut := 2) (mRef := 10)
    (es := bipEs) (compFn := bipComp) (esCon := esCon) (esDedup := esDedup)
    (lift := id) (esOut := esDedup)
    (by decide) (by decide) le_rfl (by decide) hdeg rfl hdedup_sub
    (fun e he => by simp only [esDedup, List.mem_singleton] at he; subst he; decide)
    Function.injective_id (by simp only [esDedup]; rfl)
    (fun y => ⟨⟨0, 1, 1, 0⟩, by simp [esDedup], by fin_cases y <;> simp⟩)).2
  exact ⟨hzero, hlt⟩

/-! ## 6. Multigraph and bounded-heap overflow pipeline test (`buildUndirCSR >>= ftPhaseProg`) -/

/-- Four-vertex, six-edge multigraph with self-loop `(0, 0, 1)`, parallel edges `(0, 1, 6)`,
`(0, 1, 2)`, `(0, 1, 9)`, equal-weight cross edge `(0, 2, 2)`, triangle edge `(2, 1, 4)`,
and isolated vertex `3`. With `mRef = 1`, `thresh = min 4 (2 ^ (2 / 4)) = 1`, triggering
bounded-heap overflow (`ctx.thresh < sz`) during `ftPhaseProg`. -/
@[expose] def multiOverflowEs : List (IndexedEdge 4) :=
  [⟨0, 0, 1, 10⟩, ⟨0, 1, 6, 11⟩, ⟨0, 1, 2, 12⟩, ⟨0, 1, 9, 13⟩, ⟨0, 2, 2, 14⟩, ⟨2, 1, 4, 15⟩]

/-- Memory table for `multiOverflowEs` under `Memory.State.init` (`frontier = 29`):
* `[1..25)`: stride-4 `IndexedEdge` entries at `edgeBase = 1`,
* `[25..29)`: reserved `selBufBase = 25` (`4` words). -/
@[expose] def multiOverflowWords : List ℕ :=
  [ 0, 0, 1, 10,  0, 1, 6, 11,  0, 1, 2, 12,  0, 1, 9, 13,  0, 2, 2, 14,  2, 1, 4, 15,
    0, 0, 0, 0 ]

private structure CSRPhaseArgs where
  g : GraphSlice
  mRef : ℕ
  selBufBase : ℕ
  selLen : ℕ

private word_enc_structure encCSRPhaseArgs : CSRPhaseArgs where
  g : (WordEncoding.encode (α := GraphSlice)),
  mRef : wordWords,
  selBufBase : wordWords,
  selLen : wordWords

private instance : WordEncoding CSRPhaseArgs := ⟨6, encCSRPhaseArgs⟩

private def csrAndPhaseProg (d : CSRPhaseArgs) : Memory.Prog FTPhaseOut := do
  let csr ← buildUndirCSR d.g
  ftPhaseProg ⟨d.g.numVertices, d.g.numEdges, d.mRef, d.g.edgeBase,
    csr.offBase, csr.adjBase, d.selBufBase, d.selLen⟩

private def csrAndPhaseProgSafe (w : ℕ) (d : CSRPhaseArgs) (s : Memory.State) : Prop :=
  let g := d.g
  let s₁ := (Memory.spec 0).clientState s (buildUndirCSR g)
  let csr := (Memory.spec 0).clientResult s (buildUndirCSR g)
  Fits w 16 ∧ g.edgeBase + 4 * g.numEdges ≤ s.frontier ∧
    Fits w (s.frontier + (2 * g.numVertices + 4 * g.numEdges + 1)) ∧
    (∀ j < g.numEdges,
      s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
      s.mem (g.edgeBase + 4 * j + 1) < g.numVertices) ∧
    ftPhaseProgSafe w ⟨g.numVertices, g.numEdges, d.mRef, g.edgeBase,
      csr.offBase, csr.adjBase, d.selBufBase, d.selLen⟩ s₁

private theorem realizes_csrAndPhaseProg : Realizes .exact
    csrAndPhaseProg WordEncoding.encode WordEncoding.encode csrAndPhaseProgSafe
    (fun d _ => (2 * d.mRef) / d.g.numVertices + 2) := by
  unfold csrAndPhaseProg
  realize [realizes_buildUndirCSR, realizes_ftPhaseProg]
  all_goals
    rcases h with ⟨h16, h1, h2, h3, h4⟩
    first | exact h16 | exact h1 | exact h2 | exact h3 | exact h4

/-- Composing `buildUndirCSR` and `ftPhaseProg` on `multiOverflowEs` (`mRef = 1`, `thresh = 1`)
verifies `Realizes .exact`, multigraph self-loop/parallel-edge handling, bounded-heap overflow
split (`2 ≤ res.nComp ≤ 4`), and MSF-extendable contraction. -/
private theorem ftPhaseProg_multigraph_overflow_spec :
    let s := Memory.State.init multiOverflowWords
    let args : CSRPhaseArgs := ⟨⟨4, 6, 1⟩, 1, 25, 0⟩
    let prog := csrAndPhaseProg args
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    csrAndPhaseProgSafe 16 args s ∧
    (Memory.spec 16).ValidHistory s ((Memory.spec 16).clientHistory s prog) ∧
    s'.frontier = 123 ∧
    2 ≤ res.nComp ∧ res.nComp ≤ 4 ∧
    (∃ (selEs : List (IndexedEdge 4)),
      selEs.Subperm multiOverflowEs ∧
      res.selLen = selEs.length ∧
      selEs.length + res.nComp = 4 ∧
      IsAcyclic (selEs.map IndexedEdge.toWeighted) ∧
      ∃ F_ext : List (WeightedEdge 4 ℕ),
        IsMinSpanningForest (multiOverflowEs.map IndexedEdge.toWeighted)
          (selEs.map IndexedEdge.toWeighted ++ F_ext)) ∧
    memoryCost prog s ≤ 2841 := by
  let s := Memory.State.init multiOverflowWords
  have hwf : Memory.WellFormed 16 s := Memory.wellFormed_init (by decide) (by decide)
  have hin : HoldsIndexedEdges 1 multiOverflowEs s.mem := fun i hi => by
    simp only [multiOverflowEs, List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl⟩
  have hcsr_ft := buildUndirCSR_spec (w := 16) (n := 4) (edgeBase := 1) (es := multiOverflowEs)
    (s := s) (by decide) hwf hin (by decide) (by decide)
  have hmlen : multiOverflowEs.length = 6 := rfl
  rw [hmlen] at hcsr_ft
  obtain ⟨hv₁, hc₁, hmod₁, hoff₁, hadj₁, hfr₁, hwf₁, hcsr₁⟩ :=
    framedTriple_iff_realization.mp hcsr_ft
  set csr := (Memory.spec 0).clientResult s (buildUndirCSR ⟨4, 6, 1⟩)
  set s₁ := (Memory.spec 0).clientState s (buildUndirCSR ⟨4, 6, 1⟩)
  have hfr₁' : s₁.frontier = 62 := by
    rw [hfr₁]; decide
  have hin₁ : HoldsIndexedEdges 1 multiOverflowEs s₁.mem :=
    hin.congr fun a _ ha => hmod₁.mem_eq_of_not_mem (by omega) (Set.notMem_empty a)
  have hph_ft := ftPhaseProg_spec (w := 16) (n := 4) (mRef := 1) (es := multiOverflowEs)
    (edgeBase := 1) (offBase := csr.offBase) (adjBase := csr.adjBase)
    (selBufBase := 25) (selLen0 := 0) (s := s₁)
    (by decide) hwf₁ (by decide) (by decide) (by rw [hfr₁']; decide)
    (by rw [hoff₁, hfr₁']; decide) (by rw [hadj₁, hfr₁']; decide)
    (by rw [hfr₁']; decide) (by rw [hfr₁']; decide)
    (.inr (by decide)) (.inl (by rw [hoff₁]; decide)) (.inl (by rw [hadj₁]; decide))
    hin₁ hcsr₁
  dsimp only at hph_ft
  rw [hmlen] at hph_ft
  rcases hph_ft with ⟨hsafe₂, hv₂, hfr₂, _, _, _, hnc1, hnc_le,
    ⟨selEs, compFn, hsub, hselLen, hcard, _, hac, hext, _, _, hcomp_rel, _⟩, hc₂⟩
  let args : CSRPhaseArgs := ⟨⟨4, 6, 1⟩, 1, 25, 0⟩
  have hprog_eq : csrAndPhaseProg args =
      (buildUndirCSR ⟨4, 6, 1⟩ >>= fun csrR =>
        ftPhaseProg ⟨4, 6, 1, 1, csrR.offBase, csrR.adjBase, 25, 0⟩) := rfl
  have hst_all : (Memory.spec 0).clientState s (csrAndPhaseProg args) =
      (Memory.spec 0).clientState s₁
        (ftPhaseProg ⟨4, 6, 1, 1, csr.offBase, csr.adjBase, 25, 0⟩) := by
    rw [hprog_eq, StateTransitionSpec.clientState_bind]
  have hres_all : (Memory.spec 0).clientResult s (csrAndPhaseProg args) =
      (Memory.spec 0).clientResult s₁
        (ftPhaseProg ⟨4, 6, 1, 1, csr.offBase, csr.adjBase, 25, 0⟩) := by
    rw [hprog_eq, StateTransitionSpec.clientResult_bind]
  have hv_all : (Memory.spec 16).ValidHistory s
      ((Memory.spec 16).clientHistory s (csrAndPhaseProg args)) := by
    rw [hprog_eq]; exact validHistory_bind_step hv₁ hv₂
  have hsafe_all : csrAndPhaseProgSafe 16 args s := by
    refine ⟨by decide, by decide, by decide, fun j hj => ?_, hsafe₂⟩
    have hj' : j < multiOverflowEs.length := by simpa [args, hmlen] using hj
    obtain ⟨hu, hv, _, _⟩ := hin j hj'
    rw [hu, hv]; exact ⟨(multiOverflowEs[j]'hj').u.isLt, (multiOverflowEs[j]'hj').v.isLt⟩
  have hnot3 : ∀ e ∈ selEs, e.u ≠ (3 : Fin 4) ∧ e.v ≠ (3 : Fin 4) := fun e he => by
    have hm := hsub.subset he
    simp only [multiOverflowEs, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
  have hne_03 : (edgePartition (selEs.map IndexedEdge.toWeighted)).rel 0 3 = false := by
    by_contra hrel
    have htrue : (edgePartition (selEs.map IndexedEdge.toWeighted)).rel 0 3 = true := by
      cases hh : (edgePartition (selEs.map IndexedEdge.toWeighted)).rel 0 3 <;> simp_all
    rw [rel_edgePartition_iff_eqvGen] at htrue
    have hfix : ∀ a b : Fin 4,
        Relation.EqvGen (fun x y => ∃ f ∈ selEs.map IndexedEdge.toWeighted, x = f.u ∧ y = f.v)
          a b → (a = 3 ↔ b = 3) := fun a b hab => by
      induction hab with
      | refl _ => exact Iff.rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
      | rel _ _ hf =>
        obtain ⟨f, hf_mem, rfl, rfl⟩ := hf
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hf_mem
        obtain ⟨hu, hv⟩ := hnot3 e he
        exact ⟨fun h => absurd h hu, fun h => absurd h hv⟩
    exact absurd ((hfix 0 3 htrue).mpr rfl) (by decide)
  have hcomp_ne : compFn 0 ≠ compFn 3 := fun heq => by
    have ht := (hcomp_rel 0 3).mp heq
    rw [hne_03] at ht; contradiction
  have hnc2 : 2 ≤ ((Memory.spec 0).clientResult s (csrAndPhaseProg args)).nComp := by
    rw [hres_all]
    have h0lt := (compFn 0).isLt
    have h3lt := (compFn 3).isLt
    have hval : (compFn 0).val ≠ (compFn 3).val := fun hv => hcomp_ne (Fin.ext hv)
    omega
  have hcost_all : memoryCost (csrAndPhaseProg args) s ≤ 2841 := by
    rw [hprog_eq, memoryCost_bind']
    change memoryCost (buildUndirCSR ⟨4, 6, 1⟩) s +
      memoryCost (ftPhaseProg ⟨4, 6, 1, 1, csr.offBase, csr.adjBase, 25, 0⟩) s₁ ≤ 2841
    omega
  refine ⟨hsafe_all, hv_all, by rw [hst_all, hfr₂, hfr₁'], hnc2,
    by rw [hres_all]; exact hnc_le, ⟨selEs, hsub, ?_, ?_, hac, hext⟩, hcost_all⟩
  · rw [hres_all]; simpa only [Nat.zero_add] using hselLen
  · rw [hres_all]; exact hcard

end CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.DenseCasePhase
