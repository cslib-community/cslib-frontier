/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (tests for Word-RAM MSF indexed edges and CSR)

import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.CSR
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize

/-!
# Tests for Word-RAM Minimum Spanning Forest Indexed Edges and CSR

Exercises `initIndexedEdges`, `emitMSFEdges`, `emitIndexedEdgesFromIdxs`, and `buildUndirCSR`
under `module` encapsulation across concrete triangle/disconnected graphs, multigraph boundaries
(self-loops, parallel edges, and `n = 0, m = 0`), and a composite `realize` pipeline exercising
`realizes_initIndexedEdges`, `realizes_buildUndirCSR`, `realizes_emitIndexedEdgesFromIdxs`, and
`realizes_emitMSFEdges`.
-/

-- This test module intentionally exports no declarations.
set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsCSR

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Algorithms.WordRAM.Kruskal
open Cslib.Algorithms.WordRAM.MinimumSpanningForest

/-! ## Private test setup and decode helpers -/

private def encodeIndexedEdges {n : ℕ} (es : List (IndexedEdge n)) : List ℕ :=
  es.flatMap fun e => [e.u.val, e.v.val, e.weight, e.id]

private def initFromWordsProg (words : List ℕ) : Memory.Prog ℕ := do
  let blk ← Memory.allocBlockDirty words.length
  Block.writeList blk.base words
  pure blk.base

private theorem initFromWordsProg_spec {w : ℕ} {words : List ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hfit : Fits w (s.frontier + words.length))
    (hwords : ∀ v ∈ words, Fits w v) :
    Memory.FramedTriple w s (initFromWordsProg words) (words.length + 1) ∅ fun base s' =>
      base = s.frontier ∧ s'.frontier = s.frontier + words.length ∧
      Block.HoldsList base words s'.mem ∧ Memory.WellFormed w s' := by
  let s₁ : Memory.State := ⟨s.mem, s.frontier + words.length⟩
  have hwf₁ : Memory.WellFormed w s₁ := ⟨hfit, hwf.mem_fits⟩
  have hpost : Memory.FramedTriple w s₁
      (Block.writeList s.frontier words >>= fun _ => pure s.frontier) words.length
      (Set.Ico s.frontier (s.frontier + words.length)) fun base s' =>
        base = s.frontier ∧ s'.frontier = s.frontier + words.length ∧
        Block.HoldsList base words s'.mem ∧ Memory.WellFormed w s' := by
    refine ((Block.framedTriple_writeList hwf₁ le_rfl hwords).mono le_rfl
      fun _ _ ⟨hfr, hhold, hwf'⟩ =>
        Memory.FramedTriple.pure (c := 0) ⟨rfl, hfr, hhold, hwf'⟩).bind_same
      |>.mono (Nat.add_zero _).le fun _ _ h => h
  exact ((Memory.FramedTriple.allocBlockDirty_bind hfit hpost).frame_empty_of_ge_frontier
    (S := Set.Ico s.frontier (s.frontier + words.length))
    fun _ ha => (Set.mem_Ico.mp ha).1).mono
    (by omega : words.length + 0 + 1 ≤ words.length + 1) fun _ _ h => h

private theorem holdsIndexedEdges_of_holdsList {n : ℕ} (base : ℕ) (es : List (IndexedEdge n))
    {mem : ℕ → ℕ} (h : Block.HoldsList base (encodeIndexedEdges es) mem) :
    HoldsIndexedEdges base es mem := by
  induction es generalizing base with
  | nil => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | cons e rest ih =>
    simp only [encodeIndexedEdges, List.flatMap_cons, List.cons_append, List.nil_append] at h
    obtain ⟨hu, h₁⟩ := Block.holdsList_cons_iff.mp h
    obtain ⟨hv, h₂⟩ := Block.holdsList_cons_iff.mp h₁
    obtain ⟨hw, h₃⟩ := Block.holdsList_cons_iff.mp h₂
    obtain ⟨hid, hrest⟩ := Block.holdsList_cons_iff.mp h₃
    rw [show base + 1 + 1 + 1 + 1 = base + 4 by omega] at hrest
    have hrest' : HoldsIndexedEdges (base + 4) rest mem := ih (base + 4) hrest
    intro i hi
    cases i with
    | zero => exact ⟨hu, hv, hw, hid⟩
    | succ k =>
      rcases hrest' k (Nat.lt_of_succ_lt_succ hi) with ⟨h₁, h₂, h₃, h₄⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [show base + 4 * (k + 1) = base + 4 + 4 * k by omega]; exact h₁
      · rw [show base + 4 * (k + 1) + 1 = base + 4 + 4 * k + 1 by omega]; exact h₂
      · rw [show base + 4 * (k + 1) + 2 = base + 4 + 4 * k + 2 by omega]; exact h₃
      · rw [show base + 4 * (k + 1) + 3 = base + 4 + 4 * k + 3 by omega]; exact h₄

private def mkInitStateFromWords (words : List ℕ) : Memory.State :=
  (Memory.spec 0).clientState ⟨fun _ => 0, 0⟩ (initFromWordsProg words)

private def mkInitState {n : ℕ} (es : List (IndexedEdge n)) : Memory.State :=
  mkInitStateFromWords (encodeIndexedEdges es)

private def mkInitRawState {n : ℕ} (es : List (WeightedEdge n ℕ)) : Memory.State :=
  mkInitStateFromWords (encodeEdges es)

private theorem mkInitState_spec {w n : ℕ} (es : List (IndexedEdge n))
    (hn : Fits w n) (h4m : Fits w (4 * es.length))
    (hwts : ∀ e ∈ es, Fits w e.weight ∧ Fits w e.id) :
    Memory.WellFormed w (mkInitState es) ∧
    (mkInitState es).frontier = 4 * es.length ∧
    HoldsIndexedEdges 0 es (mkInitState es).mem := by
  have hwf0 : Memory.WellFormed w ⟨fun _ => 0, 0⟩ :=
    ⟨Nat.two_pow_pos w, fun _ => Nat.two_pow_pos w⟩
  have hlen : (encodeIndexedEdges es).length = 4 * es.length := by
    clear hwf0 h4m hwts
    induction es with
    | nil => rfl
    | cons e t ih =>
      have hs : (encodeIndexedEdges (e :: t)).length = 4 + (encodeIndexedEdges t).length := by
        dsimp only [encodeIndexedEdges]
        simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil]
      rw [hs, ih, List.length_cons]
      omega
  have hfit : Fits w ((⟨fun _ => 0, 0⟩ : Memory.State).frontier +
      (encodeIndexedEdges es).length) := by
    simpa [hlen] using h4m
  have hwords : ∀ v ∈ encodeIndexedEdges es, Fits w v := by
    intro v hv
    simp only [encodeIndexedEdges, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
      or_false] at hv
    obtain ⟨e, he, rfl | rfl | rfl | rfl⟩ := hv
    · exact hn.of_le (le_of_lt e.u.isLt)
    · exact hn.of_le (le_of_lt e.v.isLt)
    · exact (hwts e he).1
    · exact (hwts e he).2
  have hft := initFromWordsProg_spec hwf0 hfit hwords
  obtain ⟨_, _, _, hb, hfr, hhold, hwf'⟩ := framedTriple_iff_realization.mp hft
  refine ⟨hwf', ?_, ?_⟩
  · simpa [mkInitState, mkInitStateFromWords, hlen] using hfr
  · rw [hb] at hhold
    exact holdsIndexedEdges_of_holdsList 0 es hhold

private theorem mkInitRawState_spec {w n : ℕ} (es : List (WeightedEdge n ℕ))
    (hn : Fits w n) (h3m : Fits w (3 * es.length))
    (hwts : ∀ e ∈ es, Fits w e.weight) :
    Memory.WellFormed w (mkInitRawState es) ∧
    (mkInitRawState es).frontier = 3 * es.length ∧
    HoldsEdges 0 es (mkInitRawState es).mem := by
  have hwf0 : Memory.WellFormed w ⟨fun _ => 0, 0⟩ :=
    ⟨Nat.two_pow_pos w, fun _ => Nat.two_pow_pos w⟩
  have hlen : (encodeEdges es).length = 3 * es.length := length_encodeEdges es
  have hfit : Fits w ((⟨fun _ => 0, 0⟩ : Memory.State).frontier +
      (encodeEdges es).length) := by
    simpa [hlen] using h3m
  have hwords : ∀ v ∈ encodeEdges es, Fits w v := by
    intro v hv
    simp only [encodeEdges, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
      or_false] at hv
    obtain ⟨e, he, rfl | rfl | rfl⟩ := hv
    · exact hn.of_le (le_of_lt e.u.isLt)
    · exact hn.of_le (le_of_lt e.v.isLt)
    · exact hwts e he
  have hft := initFromWordsProg_spec hwf0 hfit hwords
  obtain ⟨_, _, _, hb, hfr, hhold, hwf'⟩ := framedTriple_iff_realization.mp hft
  refine ⟨hwf', ?_, ?_⟩
  · simpa [mkInitRawState, mkInitStateFromWords, hlen] using hfr
  · rw [hb] at hhold
    exact holdsEdges_of_holdsList hhold

private def readIndexedEdges (base count : ℕ) (mem : ℕ → ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range count).map fun i =>
    (mem (base + 4 * i), mem (base + 4 * i + 1), mem (base + 4 * i + 2), mem (base + 4 * i + 3))

private def readRawEdges (base count : ℕ) (mem : ℕ → ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range count).map fun i =>
    (mem (base + 3 * i), mem (base + 3 * i + 1), mem (base + 3 * i + 2))

private def execWordRAM {α : Type} (s : Memory.State) (prog : Memory.Prog α) :
    α × Memory.State × ℕ :=
  ((Memory.spec 0).clientResult s prog, (Memory.spec 0).clientState s prog, memoryCost prog s)

/-! ## `IndexedEdges`: Raw-to-Indexed Initialization and Selected Emission -/

-- `initIndexedEdges` on a 3-edge triangle: output base, frontier, cost, `ValidHistory`,
-- preserved raw prefix, and decoded stride-4 edges.
example :
    let rawEdges3 : List (WeightedEdge 3 ℕ) :=
      [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 10⟩,
       ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 20⟩,
       ⟨⟨2, by decide⟩, ⟨0, by decide⟩, 5⟩]
    let s0 := mkInitRawState rawEdges3
    let r := execWordRAM s0 (initIndexedEdges 0 3)
    r.1 = 9 ∧ r.2.1.frontier = 21 ∧ r.2.2 ≤ 8 * 3 + 1 ∧
    (Memory.spec 16).ValidHistory s0 ((Memory.spec 16).clientHistory s0 (initIndexedEdges 0 3)) ∧
    readRawEdges 0 3 r.2.1.mem = [(0, 1, 10), (1, 2, 20), (2, 0, 5)] ∧
    readIndexedEdges r.1 3 r.2.1.mem = [(0, 1, 10, 0), (1, 2, 20, 1), (2, 0, 5, 2)] := by
  intro rawEdges3 s0 r
  dsimp only [r, s0, execWordRAM]
  have h16 : Fits 16 16 := by decide
  have hinit := mkInitRawState_spec (w := 16) rawEdges3 (by decide) (by decide)
    (fun e he => by simp only [rawEdges3, List.mem_cons, List.not_mem_nil, or_false] at he
                    rcases he with rfl | rfl | rfl <;> decide)
  have hft := initIndexedEdges_spec h16 hinit.1 hinit.2.2 (by rw [hinit.2.1]; decide)
    (by rw [hinit.2.1]; decide)
  have hrawLen : rawEdges3.length = 3 := rfl
  rw [hrawLen] at hft
  obtain ⟨hv, hcost, hmod, hout, hfr, _, hidx⟩ := framedTriple_iff_realization.mp hft
  have hpres : readRawEdges 0 3 r.2.1.mem = [(0, 1, 10), (1, 2, 20), (2, 0, 5)] := by
    dsimp only [r, s0, execWordRAM]
    have hraw' : HoldsEdges 0 rawEdges3 r.2.1.mem :=
      holdsEdges_frame hinit.2.2 fun a _ ha =>
        hmod.mem_eq_of_not_mem (by rw [hinit.2.1]; omega) (Set.notMem_empty _)
    rcases hraw' 0 (by decide) with ⟨h0u, h0v, h0w⟩
    rcases hraw' 1 (by decide) with ⟨h1u, h1v, h1w⟩
    rcases hraw' 2 (by decide) with ⟨h2u, h2v, h2w⟩
    dsimp only [r, s0, execWordRAM] at h0u h0v h0w h1u h1v h1w h2u h2v h2w
    simp only [readRawEdges, List.range_succ, List.range_zero, List.nil_append,
      List.map_append, List.map_cons, List.map_nil]
    rw [h0u, h0v, h0w, h1u, h1v, h1w, h2u, h2v, h2w]
    rfl
  have hdec : readIndexedEdges r.1 3 r.2.1.mem = [(0, 1, 10, 0), (1, 2, 20, 1), (2, 0, 5, 2)] := by
    dsimp only [r, s0, execWordRAM]
    rcases hidx 0 (by decide) with ⟨h0u, h0v, h0w, h0i⟩
    rcases hidx 1 (by decide) with ⟨h1u, h1v, h1w, h1i⟩
    rcases hidx 2 (by decide) with ⟨h2u, h2v, h2w, h2i⟩
    simp only [readIndexedEdges, List.range_succ, List.range_zero, List.nil_append,
      List.map_append, List.map_cons, List.map_nil]
    rw [h0u, h0v, h0w, h0i, h1u, h1v, h1w, h1i, h2u, h2v, h2w, h2i]
    rfl
  exact ⟨by rw [hout, hinit.2.1]; rfl, by rw [hfr, hinit.2.1]; rfl, hcost, hv, hpres, hdec⟩

-- `initIndexedEdges` on the empty `m = 0` graph boundary.
example :
    let s0 := mkInitRawState ([] : List (WeightedEdge 3 ℕ))
    let r := execWordRAM s0 (initIndexedEdges 0 0)
    r.1 = 0 ∧ r.2.1.frontier = 0 ∧ r.2.2 ≤ 1 ∧
    (Memory.spec 16).ValidHistory s0
      ((Memory.spec 16).clientHistory s0 (initIndexedEdges 0 0)) := by
  intro s0 r
  dsimp only [r, s0, execWordRAM]
  have h16 : Fits 16 16 := by decide
  have hinit := mkInitRawState_spec (w := 16) ([] : List (WeightedEdge 3 ℕ))
    (by decide) (by decide) (fun _ h => by simp at h)
  have hft := initIndexedEdges_spec h16 hinit.1 hinit.2.2 (by rw [hinit.2.1]; decide)
    (by rw [hinit.2.1]; decide)
  simp only [List.length_nil, Nat.mul_zero] at hft
  obtain ⟨hv, hcost, _, hout, hfr, _, _⟩ := framedTriple_iff_realization.mp hft
  exact ⟨by rw [hout, hinit.2.1]; rfl, by rw [hfr, hinit.2.1]; rfl, hcost, hv⟩

-- `emitMSFEdges` emitting selected edges `[2, 0]` from `rawEdges3`.
example :
    let rawEdges3 : List (WeightedEdge 3 ℕ) :=
      [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 10⟩,
       ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 20⟩,
       ⟨⟨2, by decide⟩, ⟨0, by decide⟩, 5⟩]
    let s0 := mkInitRawState rawEdges3
    let prog : Memory.Prog ℕ := do
      let selBase ← initFromWordsProg [2, 0]
      emitMSFEdges ⟨0, selBase, 2⟩
    let r := execWordRAM s0 prog
    r.1 = 11 ∧ r.2.1.frontier = 18 ∧ r.2.2 ≤ 23 ∧
    (Memory.spec 16).ValidHistory s0 ((Memory.spec 16).clientHistory s0 prog) ∧
    outputList r.2.1.mem r.1 = [2, 0, 5, 0, 1, 10] := by
  intro rawEdges3 s0 prog r
  dsimp only [r, execWordRAM]
  have h16 : Fits 16 16 := by decide
  have hinit := mkInitRawState_spec (w := 16) rawEdges3 (by decide) (by decide)
    (fun e he => by simp only [rawEdges3, List.mem_cons, List.not_mem_nil, or_false] at he
                    rcases he with rfl | rfl | rfl <;> decide)
  have hsel_ft := initFromWordsProg_spec (words := [2, 0]) hinit.1 (by rw [hinit.2.1]; decide)
    (fun v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
                    rcases hv with rfl | rfl <;> decide)
  have hft : Memory.FramedTriple 16 s0 prog 23 ∅ fun outBase s' =>
      outBase = 11 ∧ s'.frontier = 18 ∧ outputList s'.mem outBase = [2, 0, 5, 0, 1, 10] := by
    have hbind : Memory.FramedTriple 16 s0 prog ([2, 0].length + 1 + 20) ∅ fun outBase s' =>
        outBase = 11 ∧ s'.frontier = 18 ∧ outputList s'.mem outBase = [2, 0, 5, 0, 1, 10] := by
      refine Memory.FramedTriple.bind_same
        (Memory.Triple.mono hsel_ft le_rfl fun selBase t ⟨hm, hb, hfr, hhold, hwf'⟩ => ?_)
      refine ⟨hm, ?_⟩
      have hin' : HoldsEdges 0 rawEdges3 t.mem :=
        holdsEdges_frame hinit.2.2 fun a _ ha =>
          hm.mem_eq_of_not_mem (by rw [hinit.2.1]; omega) (Set.notMem_empty _)
      have hsel_mem : ∀ j (hj : j < ([⟨2, by decide⟩, ⟨0, by decide⟩] :
          List (Fin rawEdges3.length)).length),
          t.mem (selBase + j) = ([⟨2, by decide⟩, ⟨0, by decide⟩] :
            List (Fin rawEdges3.length))[j].val := by
        obtain ⟨h0, h1⟩ := Block.holdsList_cons_iff.mp hhold
        intro j hj
        match j with
        | 0 => exact h0
        | 1 => exact (Block.holdsList_cons_iff.mp h1).1
      have hemit := emitMSFEdges_spec (d := ⟨0, selBase, 2⟩) h16 hwf' hin'
        (by
          have hrawLen : rawEdges3.length = 3 := rfl
          dsimp only; rw [hfr, hinit.2.1, hrawLen]; decide)
        hsel_mem
        (by
          have hrawLen : rawEdges3.length = 3 := rfl
          dsimp only; rw [hb, hfr, hinit.2.1, hrawLen]; decide)
        rfl
        (by
          have hrawLen : rawEdges3.length = 3 := rfl
          dsimp only; rw [hfr, hinit.2.1, hrawLen]; decide)
      refine Memory.Triple.mono hemit (by dsimp only; omega)
        fun outBase s' ⟨hm2, hout, hfr2, _, hlist⟩ => ?_
      have hrawLen : rawEdges3.length = 3 := rfl
      refine ⟨hm2, by rw [hout, hfr, hinit.2.1, hrawLen]; rfl, ?_, ?_⟩
      · rw [hfr2, hfr, hinit.2.1, hrawLen]
        simp only [List.length_cons, List.length_nil]
      · simpa [rawEdges3, encodeEdges] using hlist
    exact hbind.mono (by decide) fun _ _ hq => hq
  obtain ⟨hv, hcost, _, hout, hfr, hlist⟩ := framedTriple_iff_realization.mp hft
  exact ⟨hout, hfr, hcost, hv, hlist⟩

-- `emitIndexedEdgesFromIdxs` on `disconnEdges` (`[2, 0]`) and `m = 0` boundaries.
example :
    let disconnEdges : List (IndexedEdge 6) :=
      [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 3, 100⟩,
       ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 4, 101⟩,
       ⟨⟨3, by decide⟩, ⟨4, by decide⟩, 2, 102⟩]
    let s0 := mkInitState disconnEdges
    let prog : Memory.Prog ℕ := do
      let selBase ← initFromWordsProg [2, 0]
      emitIndexedEdgesFromIdxs ⟨0, selBase, 2⟩
    let r := execWordRAM s0 prog
    r.1 = 14 ∧ r.2.1.frontier = 22 ∧ r.2.2 ≤ 22 ∧
    (Memory.spec 16).ValidHistory s0 ((Memory.spec 16).clientHistory s0 prog) ∧
    readIndexedEdges r.1 2 r.2.1.mem = [(3, 4, 2, 102), (0, 1, 3, 100)] ∧
    (let sE := mkInitState ([] : List (IndexedEdge 4))
     let rE := execWordRAM sE (emitIndexedEdgesFromIdxs ⟨0, 0, 0⟩)
     rE.1 = 0 ∧ rE.2.1.frontier = 0 ∧ rE.2.2 ≤ 1 ∧
     (Memory.spec 16).ValidHistory sE
       ((Memory.spec 16).clientHistory sE (emitIndexedEdgesFromIdxs ⟨0, 0, 0⟩))) := by
  intro disconnEdges s0 prog r
  dsimp only [r, execWordRAM]
  have h16 : Fits 16 16 := by decide
  have hinit := mkInitState_spec (w := 16) disconnEdges (by decide) (by decide)
    (fun e he => by simp only [disconnEdges, List.mem_cons, List.not_mem_nil, or_false] at he
                    rcases he with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩)
  have hsel_ft := initFromWordsProg_spec (words := [2, 0]) hinit.1 (by rw [hinit.2.1]; decide)
    (fun v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
                    rcases hv with rfl | rfl <;> decide)
  have hft : Memory.FramedTriple 16 s0 prog 22 ∅ fun outBase s' =>
      outBase = 14 ∧ s'.frontier = 22 ∧
      HoldsIndexedEdges outBase [disconnEdges[2], disconnEdges[0]] s'.mem := by
    have hbind : Memory.FramedTriple 16 s0 prog ([2, 0].length + 1 + 19) ∅ fun outBase s' =>
        outBase = 14 ∧ s'.frontier = 22 ∧
        HoldsIndexedEdges outBase [disconnEdges[2], disconnEdges[0]] s'.mem := by
      refine Memory.FramedTriple.bind_same
        (Memory.Triple.mono hsel_ft le_rfl fun selBase t ⟨hm, hb, hfr, hhold, hwf'⟩ => ?_)
      refine ⟨hm, ?_⟩
      have hin' : HoldsIndexedEdges 0 disconnEdges t.mem :=
        hinit.2.2.congr fun a _ ha => hm.mem_eq_of_not_mem (by rw [hinit.2.1]; omega)
          (Set.notMem_empty _)
      have hsel_mem : ∀ j (hj : j < ([⟨2, by decide⟩, ⟨0, by decide⟩] :
          List (Fin disconnEdges.length)).length),
          t.mem (selBase + j) = ([⟨2, by decide⟩, ⟨0, by decide⟩] :
            List (Fin disconnEdges.length))[j].val := by
        obtain ⟨h0, h1⟩ := Block.holdsList_cons_iff.mp hhold
        intro j hj
        match j with
        | 0 => exact h0
        | 1 => exact (Block.holdsList_cons_iff.mp h1).1
      have hemit := emitIndexedEdgesFromIdxs_spec (d := ⟨0, selBase, 2⟩) h16 hwf' hin'
        (by
          have hdisLen : disconnEdges.length = 3 := rfl
          dsimp only; rw [hfr, hinit.2.1, hdisLen]; omega)
        hsel_mem
        (by
          have hdisLen : disconnEdges.length = 3 := rfl
          dsimp only; rw [hb, hfr, hinit.2.1, hdisLen]
          simp only [List.length_cons, List.length_nil]; omega)
        rfl
        (by
          have hdisLen : disconnEdges.length = 3 := rfl
          dsimp only; rw [hfr, hinit.2.1, hdisLen]; decide)
      refine Memory.Triple.mono hemit (by dsimp only; omega)
        fun outBase s' ⟨hm2, hout, hfr2, _, hedges⟩ => ?_
      have hdisLen : disconnEdges.length = 3 := rfl
      refine ⟨hm2, by rw [hout, hfr, hinit.2.1, hdisLen]; rfl, ?_, ?_⟩
      · rw [hfr2, hfr, hinit.2.1, hdisLen]
        simp only [List.length_cons, List.length_nil]
      · simpa using hedges
    exact hbind.mono (by decide) fun _ _ hq => hq
  obtain ⟨hv, hcost, _, hout, hfr, hedges⟩ := framedTriple_iff_realization.mp hft
  have hdec : readIndexedEdges r.1 2 r.2.1.mem = [(3, 4, 2, 102), (0, 1, 3, 100)] := by
    dsimp only [r, execWordRAM]
    rcases hedges 0 (by decide) with ⟨h0u, h0v, h0w, h0i⟩
    rcases hedges 1 (by decide) with ⟨h1u, h1v, h1w, h1i⟩
    simp only [readIndexedEdges, List.range_succ, List.range_zero, List.nil_append,
      List.map_append, List.map_cons, List.map_nil]
    rw [h0u, h0v, h0w, h0i, h1u, h1v, h1w, h1i]
    rfl
  have hinitE := mkInitState_spec (w := 16) ([] : List (IndexedEdge 4))
    (by decide) (by decide) (fun _ h => by simp at h)
  have hftE := emitIndexedEdgesFromIdxs_spec (d := ⟨0, 0, 0⟩)
    (idxs := ([] : List (Fin ([] : List (IndexedEdge 4)).length)))
    h16 hinitE.1 hinitE.2.2 (by rw [hinitE.2.1]; decide) (fun _ hj => by simp at hj)
    (by rw [hinitE.2.1]; decide) rfl (by rw [hinitE.2.1]; decide)
  obtain ⟨hvE, hcostE, _, houtE, hfrE, _, _⟩ := framedTriple_iff_realization.mp hftE
  exact ⟨hout, hfr, hcost, hv, hdec, by simp [houtE, hinitE.2.1], by simp [hfrE, hinitE.2.1],
    hcostE, hvE⟩

/-! ## `CSR`: Forest, Multigraph Self-Loops / Parallel Edges, and `n = 0, m = 0` -/

-- `buildUndirCSR` on disconnected 6-vertex graph `disconnEdges` (including isolated vertex `5`),
-- checking `offBase`, `adjBase`, frontier, cost, `ValidHistory`, and `mem_slice_iff`.
example :
    let disconnEdges : List (IndexedEdge 6) :=
      [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 3, 100⟩,
       ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 4, 101⟩,
       ⟨⟨3, by decide⟩, ⟨4, by decide⟩, 2, 102⟩]
    let s0 := mkInitState disconnEdges
    let g : GraphSlice := ⟨6, 3, 0⟩
    let r := execWordRAM s0 (buildUndirCSR g)
    r.1.offBase = 12 ∧ r.1.adjBase = 19 ∧ r.2.1.frontier = 37 ∧
    r.2.2 ≤ 16 * 3 + 5 * 6 + 6 ∧
    (Memory.spec 16).ValidHistory s0 ((Memory.spec 16).clientHistory s0 (buildUndirCSR g)) ∧
    HoldsUndirCSR r.1.offBase r.1.adjBase disconnEdges r.2.1.mem ∧
    (0, 0) ∈ (List.range (r.2.1.mem (r.1.offBase + 2) - r.2.1.mem (r.1.offBase + 1))).map
      (fun k =>
        let p := r.2.1.mem (r.1.offBase + 1) + k
        (r.2.1.mem (r.1.adjBase + 2 * p), r.2.1.mem (r.1.adjBase + 2 * p + 1))) ∧
    (2, 1) ∈ (List.range (r.2.1.mem (r.1.offBase + 2) - r.2.1.mem (r.1.offBase + 1))).map
      (fun k =>
        let p := r.2.1.mem (r.1.offBase + 1) + k
        (r.2.1.mem (r.1.adjBase + 2 * p), r.2.1.mem (r.1.adjBase + 2 * p + 1))) ∧
    ∀ nb eIdx, ¬ (nb, eIdx) ∈
      (List.range (r.2.1.mem (r.1.offBase + 6) - r.2.1.mem (r.1.offBase + 5))).map
        (fun k =>
          let p := r.2.1.mem (r.1.offBase + 5) + k
          (r.2.1.mem (r.1.adjBase + 2 * p), r.2.1.mem (r.1.adjBase + 2 * p + 1))) := by
  intro disconnEdges s0 g r
  dsimp only [r, s0, g, execWordRAM]
  have h16 : Fits 16 16 := by decide
  have hinit := mkInitState_spec (w := 16) disconnEdges (by decide) (by decide)
    (fun e he => by simp only [disconnEdges, List.mem_cons, List.not_mem_nil, or_false] at he
                    rcases he with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩)
  have hft := buildUndirCSR_spec h16 hinit.1 hinit.2.2 (by rw [hinit.2.1]; decide)
    (by rw [hinit.2.1]; decide)
  have hlen3 : disconnEdges.length = 3 := rfl
  rw [hlen3] at hft
  obtain ⟨hv, hcost, _, hoff, hadj, hfr, _, hcsr⟩ := framedTriple_iff_realization.mp hft
  refine ⟨by rw [hoff, hinit.2.1]; rfl, by rw [hadj, hinit.2.1]; rfl,
    by rw [hfr, hinit.2.1]; rfl, hcost, hv, hcsr, ?_, ?_, ?_⟩
  · exact (hcsr.mem_slice_iff ⟨1, by decide⟩ 0 0).mpr ⟨⟨0, by decide⟩, rfl, .inr ⟨rfl, rfl⟩⟩
  · exact (hcsr.mem_slice_iff ⟨1, by decide⟩ 2 1).mpr ⟨⟨1, by decide⟩, rfl, .inl ⟨rfl, rfl⟩⟩
  · intro nb eIdx hm
    obtain ⟨i, _, h_uv⟩ := (hcsr.mem_slice_iff ⟨5, by decide⟩ nb eIdx).mp hm
    fin_cases i <;> simp [disconnEdges] at h_uv

-- `buildUndirCSR` on empty `m = 0` (`n = 3` and `n = 0`) boundaries.
example :
    let s3 := mkInitState ([] : List (IndexedEdge 3))
    let r3 := execWordRAM s3 (buildUndirCSR ⟨3, 0, 0⟩)
    let s0 := mkInitState ([] : List (IndexedEdge 0))
    let r0 := execWordRAM s0 (buildUndirCSR ⟨0, 0, 0⟩)
    r3.2.1.frontier = 7 ∧
    (Memory.spec 16).ValidHistory s3 ((Memory.spec 16).clientHistory s3 (buildUndirCSR ⟨3, 0, 0⟩)) ∧
    (∀ k ≤ 3, r3.2.1.mem (r3.1.offBase + k) = 0) ∧
    r0.2.1.frontier = 1 ∧
    (Memory.spec 16).ValidHistory s0 ((Memory.spec 16).clientHistory s0 (buildUndirCSR ⟨0, 0, 0⟩)) ∧
    r0.2.1.mem r0.1.offBase = 0 := by
  intro s3 r3 s0 r0
  dsimp only [r3, s3, r0, s0, execWordRAM]
  have h16 : Fits 16 16 := by decide
  have hinit3 := mkInitState_spec (w := 16) ([] : List (IndexedEdge 3))
    (by decide) (by decide) (fun _ h => by simp at h)
  have hft3 := buildUndirCSR_spec h16 hinit3.1 hinit3.2.2 (by rw [hinit3.2.1]; decide)
    (by rw [hinit3.2.1]; decide)
  simp only [List.length_nil, Nat.mul_zero] at hft3
  obtain ⟨hv3, _, _, _, _, hfr3, _, hcsr3⟩ := framedTriple_iff_realization.mp hft3
  have hinit0 := mkInitState_spec (w := 16) ([] : List (IndexedEdge 0))
    (by decide) (by decide) (fun _ h => by simp at h)
  have hft0 := buildUndirCSR_spec h16 hinit0.1 hinit0.2.2 (by rw [hinit0.2.1]; decide)
    (by rw [hinit0.2.1]; decide)
  simp only [List.length_nil, Nat.mul_zero] at hft0
  obtain ⟨hv0, _, _, _, _, hfr0, _, hcsr0⟩ := framedTriple_iff_realization.mp hft0
  refine ⟨by rw [hfr3, hinit3.2.1]; rfl, hv3, fun k hk => ?_,
    by rw [hfr0, hinit0.2.1]; rfl, hv0, hcsr0.off_zero⟩
  have hle := hcsr3.offset_le_end k hk
  simp only [List.length_nil, Nat.mul_zero, Nat.le_zero] at hle
  exact hle

-- Multigraph `buildUndirCSR` witness with self-loop `0 — 0` (id `0`) and parallel edges
-- `0 — 1` (ids `1, 2`) on `3` vertices (isolated vertex `2`), verifying exact CSR offsets and
-- half-edge multiplicities in vertex slices.
private def multiEdges3 : List (IndexedEdge 3) :=
  [⟨⟨0, by decide⟩, ⟨0, by decide⟩, 7, 50⟩,
   ⟨⟨0, by decide⟩, ⟨1, by decide⟩, 5, 51⟩,
   ⟨⟨0, by decide⟩, ⟨1, by decide⟩, 9, 52⟩]

example :
    let s0 := mkInitState multiEdges3
    let r := execWordRAM s0 (buildUndirCSR ⟨3, 3, 0⟩)
    let slice (u : ℕ) :=
      (List.range (r.2.1.mem (r.1.offBase + u + 1) - r.2.1.mem (r.1.offBase + u))).map
        fun k =>
          let p := r.2.1.mem (r.1.offBase + u) + k
          (r.2.1.mem (r.1.adjBase + 2 * p), r.2.1.mem (r.1.adjBase + 2 * p + 1))
    r.1.offBase = 12 ∧ r.1.adjBase = 16 ∧ r.2.1.frontier = 31 ∧
    r.2.2 ≤ 16 * 3 + 5 * 3 + 6 ∧
    (Memory.spec 16).ValidHistory s0 ((Memory.spec 16).clientHistory s0 (buildUndirCSR ⟨3, 3, 0⟩)) ∧
    r.2.1.mem (r.1.offBase + 0) = 0 ∧ r.2.1.mem (r.1.offBase + 1) = 4 ∧
    r.2.1.mem (r.1.offBase + 2) = 6 ∧ r.2.1.mem (r.1.offBase + 3) = 6 ∧
    (slice 0).count (0, 0) = 2 ∧ (slice 0).count (1, 1) = 1 ∧ (slice 0).count (1, 2) = 1 ∧
    (slice 1).count (0, 1) = 1 ∧ (slice 1).count (0, 2) = 1 ∧ slice 2 = [] := by
  intro s0 r slice
  dsimp only [r, s0, slice, execWordRAM]
  have h16 : Fits 16 16 := by decide
  have hinit := mkInitState_spec (w := 16) multiEdges3 (by decide) (by decide)
    (fun e he => by simp only [multiEdges3, List.mem_cons, List.not_mem_nil, or_false] at he
                    rcases he with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩)
  have hft := buildUndirCSR_spec h16 hinit.1 hinit.2.2 (by rw [hinit.2.1]; decide)
    (by rw [hinit.2.1]; decide)
  have hlen3 : multiEdges3.length = 3 := rfl
  rw [hlen3] at hft
  obtain ⟨hv, hcost, _, hoff, hadj, hfr, _, hcsr⟩ := framedTriple_iff_realization.mp hft
  have h0 := hcsr.off_zero
  have h3 := hcsr.off_end
  have hp0 := hcsr.adj_perm ⟨0, by decide⟩
  have hp1 := hcsr.adj_perm ⟨1, by decide⟩
  have hp2 := hcsr.adj_perm ⟨2, by decide⟩
  have hl0 := hp0.length_eq
  have hl1 := hp1.length_eq
  have hr0 : ((((List.finRange multiEdges3.length).filter
      (fun i => decide (multiEdges3[i.val].u = ⟨0, by decide⟩))).map
      (fun i => (multiEdges3[i.val].v.val, i.val))) ++
      (((List.finRange multiEdges3.length).filter
      (fun i => decide (multiEdges3[i.val].v = ⟨0, by decide⟩))).map
      (fun i => (multiEdges3[i.val].u.val, i.val)))).length = 4 := rfl
  have hr1 : ((((List.finRange multiEdges3.length).filter
      (fun i => decide (multiEdges3[i.val].u = ⟨1, by decide⟩))).map
      (fun i => (multiEdges3[i.val].v.val, i.val))) ++
      (((List.finRange multiEdges3.length).filter
      (fun i => decide (multiEdges3[i.val].v = ⟨1, by decide⟩))).map
      (fun i => (multiEdges3[i.val].u.val, i.val)))).length = 2 := rfl
  simp only [List.length_map, List.length_range, Nat.add_assoc, Nat.add_zero, Nat.reduceAdd]
    at hl0 hl1
  have hoff0 :
      ((Memory.spec 0).clientState (mkInitState multiEdges3) (buildUndirCSR ⟨3, 3, 0⟩)).mem
        (((Memory.spec 0).clientResult (mkInitState multiEdges3)
          (buildUndirCSR ⟨3, 3, 0⟩)).offBase + 0) = 0 := h0
  have hoff1 :
      ((Memory.spec 0).clientState (mkInitState multiEdges3) (buildUndirCSR ⟨3, 3, 0⟩)).mem
        (((Memory.spec 0).clientResult (mkInitState multiEdges3)
          (buildUndirCSR ⟨3, 3, 0⟩)).offBase + 1) = 4 := by
    have h0' :
        ((Memory.spec 0).clientState (mkInitState multiEdges3) (buildUndirCSR ⟨3, 3, 0⟩)).mem
          ((Memory.spec 0).clientResult (mkInitState multiEdges3)
            (buildUndirCSR ⟨3, 3, 0⟩)).offBase = 0 := h0
    have := hl0.trans hr0
    omega
  have hoff2 :
      ((Memory.spec 0).clientState (mkInitState multiEdges3) (buildUndirCSR ⟨3, 3, 0⟩)).mem
        (((Memory.spec 0).clientResult (mkInitState multiEdges3)
          (buildUndirCSR ⟨3, 3, 0⟩)).offBase + 2) = 6 := by
    have := hl1.trans hr1
    omega
  have hoff3 :
      ((Memory.spec 0).clientState (mkInitState multiEdges3) (buildUndirCSR ⟨3, 3, 0⟩)).mem
        (((Memory.spec 0).clientResult (mkInitState multiEdges3)
          (buildUndirCSR ⟨3, 3, 0⟩)).offBase + 3) = 6 := by
    simpa [hlen3] using h3
  have hc00 := (hp0.count_eq (0, 0)).trans (show _ = 2 by decide)
  have hc01 := (hp0.count_eq (1, 1)).trans (show _ = 1 by decide)
  have hc02 := (hp0.count_eq (1, 2)).trans (show _ = 1 by decide)
  have hc11 := (hp1.count_eq (0, 1)).trans (show _ = 1 by decide)
  have hc12 := (hp1.count_eq (0, 2)).trans (show _ = 1 by decide)
  refine ⟨by rw [hoff, hinit.2.1]; rfl, by rw [hadj, hinit.2.1]; rfl,
    by rw [hfr, hinit.2.1]; rfl, hcost, hv, hoff0, hoff1, hoff2, hoff3,
    hc00, hc01, hc02, hc11, hc12, ?_⟩
  simp only [Nat.add_assoc, hoff2, hoff3]; simp

/-! ## Composite `realize` pipeline over `WordEncoding` boundaries -/

private def csrPipelineProg (d : (ℕ × ℕ) × (ℕ × (ℕ × ℕ))) :
    Memory.Prog (UndirCSR × ℕ × ℕ) := do
  let idxBase ← initIndexedEdges d.1.1 d.2.1
  let csr ← buildUndirCSR ⟨d.1.2, d.2.1, idxBase⟩
  let subBase ← emitIndexedEdgesFromIdxs ⟨idxBase, d.2.2.1, d.2.2.2⟩
  let rawOut ← emitMSFEdges ⟨d.1.1, d.2.2.1, d.2.2.2⟩
  pure (csr, subBase, rawOut)

private def csrPipelineRawPre (w : ℕ) (d : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)))
    (s : Memory.State) : Prop :=
  let idxBase := (Memory.spec 0).clientResult s (initIndexedEdges d.1.1 d.2.1)
  let s1 := (Memory.spec 0).clientState s (initIndexedEdges d.1.1 d.2.1)
  let s2 := (Memory.spec 0).clientState s1 (buildUndirCSR ⟨d.1.2, d.2.1, idxBase⟩)
  let s3 := (Memory.spec 0).clientState s2
    (emitIndexedEdgesFromIdxs ⟨idxBase, d.2.2.1, d.2.2.2⟩)
  Fits w 16 ∧
  d.1.1 + 3 * d.2.1 ≤ s.frontier ∧
  Fits w (s.frontier + 4 * d.2.1) ∧
  idxBase + 4 * d.2.1 ≤ s1.frontier ∧
  Fits w (s1.frontier + (2 * d.1.2 + 4 * d.2.1 + 1)) ∧
  (∀ j < d.2.1, s1.mem (idxBase + 4 * j) < d.1.2 ∧ s1.mem (idxBase + 4 * j + 1) < d.1.2) ∧
  d.2.2.1 + d.2.2.2 ≤ s2.frontier ∧
  Fits w (s2.frontier + 4 * d.2.2.2) ∧
  (∀ j < d.2.2.2, idxBase + 4 * s2.mem (d.2.2.1 + j) + 4 ≤ s2.frontier) ∧
  d.2.2.1 + d.2.2.2 ≤ s3.frontier ∧
  Fits w (s3.frontier + (3 * d.2.2.2 + 1)) ∧
  ∀ j < d.2.2.2, d.1.1 + 3 * s3.mem (d.2.2.1 + j) + 3 ≤ s3.frontier

-- Cross-module `realize` composition exercising `encGraphSlice`, `encSelectedEdgesArgs`,
-- `encUndirCSR`, and all four `realizes_*` certificates end-to-end with `work = 0`.
example : Realizes .exact csrPipelineProg
    WordEncoding.encode WordEncoding.encode
    (fun w d s =>
      Fits w 16 ∧
      d.1.1 + 3 * d.2.1 ≤ s.frontier ∧
      d.2.2.1 + d.2.2.2 ≤ s.frontier ∧
      Fits w (s.frontier + 4 * d.2.1 + (2 * d.1.2 + 4 * d.2.1 + 1) +
        4 * d.2.2.2 + (3 * d.2.2.2 + 1)) ∧
      (∀ j < d.2.1, s.mem (d.1.1 + 3 * j) < d.1.2 ∧ s.mem (d.1.1 + 3 * j + 1) < d.1.2) ∧
      ∀ j < d.2.2.2, s.mem (d.2.2.1 + j) < d.2.1)
    (fun _ _ => 0) := by
  have hraw : Realizes .exact csrPipelineProg WordEncoding.encode WordEncoding.encode
      csrPipelineRawPre (fun _ _ => 0) := by
    unfold csrPipelineProg
    realize [realizes_initIndexedEdges, realizes_buildUndirCSR,
      realizes_emitIndexedEdgesFromIdxs, realizes_emitMSFEdges]
    all_goals
      rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
      first
      | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | exact h6
      | exact h7 | exact h8 | exact h9 | exact h10 | exact h11 | exact h12
  refine hraw.consequence (fun w d s _ hmem h => ?_) (fun _ _ => le_rfl)
  rcases d with ⟨⟨inBase, n⟩, ⟨m, ⟨selBase, k⟩⟩⟩
  obtain ⟨h16, hin_lt, hsel_lt, hfit, hedges, hsel_lt_m⟩ := h
  dsimp only at hin_lt hsel_lt hfit hedges hsel_lt_m
  dsimp only [csrPipelineRawPre]
  let es : List (WeightedEdge n ℕ) :=
    List.ofFn fun i : Fin m =>
      ⟨⟨s.mem (inBase + 3 * i.val), (hedges i.val i.isLt).1⟩,
       ⟨s.mem (inBase + 3 * i.val + 1), (hedges i.val i.isLt).2⟩,
       s.mem (inBase + 3 * i.val + 2)⟩
  have hlen : es.length = m := List.length_ofFn
  have hraw_in : HoldsEdges inBase es s.mem := fun i hi => by simp [es]
  have hft1 := initIndexedEdges_spec h16 hmem hraw_in (by simpa [hlen] using hin_lt)
    (hfit.of_le (by simp [hlen]; omega))
  rw [hlen] at hft1
  obtain ⟨_, _, hmod1, hidx_eq, hfr1, hwf1, hidx_holds⟩ :=
    framedTriple_iff_realization.mp hft1
  set idxBase := (Memory.spec 0).clientResult s (initIndexedEdges inBase m)
  set s1 := (Memory.spec 0).clientState s (initIndexedEdges inBase m)
  let ies : List (IndexedEdge n) := es.mapIdx fun i e => ⟨e.u, e.v, e.weight, i⟩
  have hlen_i : ies.length = m := by simp [ies, hlen]
  have hft2 := buildUndirCSR_spec (n := n) (edgeBase := idxBase) (es := ies)
    h16 hwf1 hidx_holds
    (by rw [hlen_i, hidx_eq, hfr1])
    (by rw [hlen_i, hfr1]; exact hfit.of_le (by omega))
  rw [hlen_i] at hft2
  obtain ⟨_, _, hmod2, _, _, hfr2, hwf2, _⟩ := framedTriple_iff_realization.mp hft2
  set s2 := (Memory.spec 0).clientState s1 (buildUndirCSR ⟨n, m, idxBase⟩)
  have hsel_s2 : ∀ j < k, s2.mem (selBase + j) = s.mem (selBase + j) := fun j hj => by
    have hm2 : s2.mem (selBase + j) = s1.mem (selBase + j) :=
      hmod2.mem_eq_of_not_mem (by rw [hfr1]; omega) (Set.notMem_empty _)
    have hm1 : s1.mem (selBase + j) = s.mem (selBase + j) :=
      hmod1.mem_eq_of_not_mem (by omega) (Set.notMem_empty _)
    exact hm2.trans hm1
  have hidx_holds2 : HoldsIndexedEdges idxBase ies s2.mem :=
    hidx_holds.congr fun a _ ha2 =>
      hmod2.mem_eq_of_not_mem (by rw [hfr1]; rw [hlen_i, hidx_eq] at ha2; omega)
        (Set.notMem_empty _)
  let selFin : List (Fin ies.length) :=
    List.ofFn fun j : Fin k => ⟨s.mem (selBase + j.val), hlen_i ▸ hsel_lt_m j.val j.isLt⟩
  have hlen_sel : selFin.length = k := List.length_ofFn
  have hft3 := emitIndexedEdgesFromIdxs_spec (d := ⟨idxBase, selBase, k⟩)
    (es := ies) (idxs := selFin) h16 hwf2 hidx_holds2
    (by dsimp only; rw [hfr2, hfr1, hidx_eq, hlen_i]; omega)
    (fun j hj => by rw [hsel_s2 j (hlen_sel ▸ hj)]; simp [selFin])
    (by dsimp only; rw [hfr2, hfr1]; omega)
    hlen_sel.symm
    (by dsimp only; rw [hfr2, hfr1]; exact hfit.of_le (by omega))
  obtain ⟨_, _, hmod3, _, hfr3, _, _⟩ := framedTriple_iff_realization.mp hft3
  dsimp only at hfr3
  set s3 := (Memory.spec 0).clientState s2 (emitIndexedEdgesFromIdxs ⟨idxBase, selBase, k⟩)
  refine ⟨h16, hin_lt, hfit.of_le (by omega),
    by rw [hidx_eq, hfr1],
    by rw [hfr1]; exact hfit.of_le (by omega),
    fun j hj => ?_,
    by rw [hfr2, hfr1]; omega,
    by rw [hfr2, hfr1]; exact hfit.of_le (by omega),
    fun j hj => ?_,
    by rw [hfr3, hfr2, hfr1]; omega,
    by rw [hfr3, hfr2, hfr1]; exact hfit.of_le (by omega),
    fun j hj => ?_⟩
  · have hj' : j < ies.length := hlen_i.symm ▸ hj
    rw [(hidx_holds j hj').1, (hidx_holds j hj').2.1]
    exact ⟨ies[j].u.isLt, ies[j].v.isLt⟩
  · have hlt := hsel_lt_m j hj
    rw [hsel_s2 j hj, hidx_eq, hfr2, hfr1]; omega
  · have hm3 : s3.mem (selBase + j) = s2.mem (selBase + j) :=
      hmod3.mem_eq_of_not_mem (by rw [hfr2, hfr1]; omega) (Set.notMem_empty _)
    have hlt := hsel_lt_m j hj
    rw [hm3, hsel_s2 j hj, hfr3, hfr2, hfr1]; omega

end CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsCSR
