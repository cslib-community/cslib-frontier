/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.IndexedEdges

/-!
# Shared Word-RAM Minimum Spanning Forest GraphOps Test Support

Provides concrete Word-RAM test setup and decoding helpers over stride-4 `IndexedEdge` layouts
shared by `GraphOpsCSR` and `GraphOpsComponents`.
-/

public section

namespace CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsTestSupport

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal
open Cslib.Algorithms.WordRAM.MinimumSpanningForest

/-- Flatten `es : List (IndexedEdge n)` into stride-4 words `[u, v, weight, id, ...]`. -/
@[expose] def encodeIndexedEdges {n : ℕ} (es : List (IndexedEdge n)) : List ℕ :=
  es.flatMap fun e => [e.u.val, e.v.val, e.weight, e.id]

/-- Allocate `words.length` cells and write `words` consecutively via `Block.writeList`. -/
@[expose] def initFromWordsProg (words : List ℕ) : Memory.Prog ℕ := do
  let blk ← Memory.allocBlockDirty words.length
  Block.writeList blk.base words
  pure blk.base

/-- Framed specification for `initFromWordsProg` allocating and initializing `words`. -/
theorem initFromWordsProg_spec {w : ℕ} {words : List ℕ} {s : Memory.State}
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
    fun _ ha => ha.1).mono (by omega : words.length + 0 + 1 ≤ words.length + 1)
    fun _ _ h => h

/-- Convert `Block.HoldsList base (encodeIndexedEdges es) mem` into
`HoldsIndexedEdges base es mem`. -/
theorem holdsIndexedEdges_of_holdsList {n : ℕ} (base : ℕ) (es : List (IndexedEdge n))
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

/-- Build an initial `Memory.State` containing `words` at `[0, words.length)`. -/
@[expose] def mkInitStateFromWords (words : List ℕ) : Memory.State :=
  (Memory.spec 0).clientState ⟨fun _ => 0, 0⟩ (initFromWordsProg words)

/-- Build an initial `Memory.State` holding `es : List (IndexedEdge n)` at address `0`. -/
@[expose] def mkInitState {n : ℕ} (es : List (IndexedEdge n)) : Memory.State :=
  mkInitStateFromWords (encodeIndexedEdges es)

/-- Specification of `mkInitState`: produces a well-formed state at frontier `4 * es.length`
holding `es` at address `0`. -/
theorem mkInitState_spec {w n : ℕ} (es : List (IndexedEdge n))
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

/-- Decode `count` consecutive stride-4 `(u, v, weight, id)` edge records from `mem` at `base`. -/
@[expose] def readIndexedEdges (base count : ℕ) (mem : ℕ → ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range count).map fun i =>
    (mem (base + 4 * i), mem (base + 4 * i + 1), mem (base + 4 * i + 2), mem (base + 4 * i + 3))

/-- Execute `prog` from `s` with unbounded client semantics, returning
`(result, finalState, totalCost)`. -/
@[expose] def execWordRAM {α : Type} (s : Memory.State) (prog : Memory.Prog α) :
    α × Memory.State × ℕ :=
  ((Memory.spec 0).clientResult s prog, (Memory.spec 0).clientState s prog, memoryCost prog s)

/-- The empty edge set is a minimum spanning forest of an empty graph. -/
theorem isMinSpanningForest_nil {n : ℕ} :
    IsMinSpanningForest (n := n) ([] : List (WeightedEdge n ℕ)) [] :=
  ⟨⟨List.Subperm.refl _, isAcyclic_nil, rfl⟩, fun _ hF' => by
    rw [List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hF'.1.length_le)]⟩

end CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsTestSupport
