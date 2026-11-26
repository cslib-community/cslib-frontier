/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (tests for DecisionTree.Layout and DecisionTree.PrecompKruskal)

import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.DecisionTree.PrecompKruskal

/-!
# Tests for Word-RAM Decision-Tree Layouts and Kruskal Precomputation

Exercises `dtThreshold`, `dtPrecompCost`, `dtGraphMask`, `walkCompleteTree_eval`,
`skelToTree_isComplete`, and the `*_spec` / `realizes_*` interfaces of `dtFillAllPairsProg`,
`dtFillPowProg`, `dtDecodeMaskProg`, and `dtKruskalMaskProg` under `module` encapsulation,
including `numV = 0` / `len = 0` / `e = 0` empty-graph boundary witnesses.
-/

-- This test module intentionally exports no declarations.
set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.DecisionTreeLayout

open Cslib.WordRAM
open Cslib.WordRAM.Realization
open Cslib.DataStructure
open Cslib.Query.MinimumSpanningForest
open Cslib.Algorithms.WordRAM.MinimumSpanningForest

/-! ## `DecisionTree.Layout`: Threshold, Bitmask, and Complete-Tree Evaluation -/

-- Threshold lower/cost bounds and `dtGraphMask` bit/bound properties on a 3-vertex triangle.
example :
    1 ≤ dtThreshold 0 ∧
    dtPrecompCost (dtThreshold 128) ≤ 128 ∧
    (let es : List (Fin 3 × Fin 3) :=
      [(⟨0, by decide⟩, ⟨1, by decide⟩), (⟨1, by decide⟩, ⟨2, by decide⟩)]
     dtGraphMask es < 2 ^ Nat.choose 3 2 ∧
     (dtGraphMask es).testBit (edgePairIdx 1 2) = true) := by
  refine ⟨dtThreshold_ge_one 0, dtPrecompCost_dtThreshold_le (by decide), ?_⟩
  let es : List (Fin 3 × Fin 3) :=
    [(⟨0, by decide⟩, ⟨1, by decide⟩), (⟨1, by decide⟩, ⟨2, by decide⟩)]
  refine ⟨dtGraphMask_lt es (fun e he => by
    simp only [es, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> decide), ?_⟩
  rw [dtGraphMask_testBit, decide_eq_true_iff]
  exact ⟨(⟨1, by decide⟩, ⟨2, by decide⟩), by simp, rfl⟩

-- `skelToTree_isComplete` and `walkCompleteTree_eval` on a depth-1 tree over `2` edges.
example (p : Equiv.Perm (Fin 2)) (cmp : Fin 2 → Fin 2 → Bool)
    (hcmp : ∀ a b : Fin 2, cmp a b = true ↔ (p a).val < (p b).val) :
    (skelToTree 2 le_rfl 1 0 (fun k => k + 1) 1 1).IsComplete 1 ∧
    (let l0 : Finset (Fin 2) := {⟨0, by decide⟩}
     let l1 : Finset (Fin 2) := {⟨1, by decide⟩}
     let T : MSFDT 2 := .node ⟨0, by decide⟩ ⟨1, by decide⟩ (.leaf l0) (.leaf l1)
     let mem : ℕ → ℕ := fun a =>
       if a = 0 then 0 else if a = 1 then 1
       else if a = 10 then maskOfFinset l0 else if a = 11 then maskOfFinset l1 else 0
     let endNode := walkCompleteTree 0 10 mem cmp 1 1
     2 ≤ endNode ∧ endNode < 4 ∧
     mem (10 + (endNode - 2)) = maskOfFinset (T.eval p)) := by
  refine ⟨skelToTree_isComplete 2 le_rfl 1 0 (fun k => k + 1) 1 1, ?_⟩
  intro l0 l1 T mem endNode
  have hhold : HoldsCompleteTree 1 0 10 1 1 mem T := by
    refine holdsCompleteTree_node.mpr ⟨by decide, by decide, ?_, ?_, ?_, ?_⟩
    · simp [mem]
    · simp [mem]
    · exact holdsCompleteTree_leaf.mpr ⟨by decide, by decide, by simp [mem]⟩
    · exact holdsCompleteTree_leaf.mpr ⟨by decide, by decide, by simp [mem]⟩
  simpa using walkCompleteTree_eval p cmp hcmp hhold

/-! ## `DecisionTree.PrecompKruskal`: Enumeration, Power Table, Decoding, and Kruskal -/

-- `dtFillAllPairsProg_spec`, `realizes_dtFillAllPairsProg`, and empty `numV = 0` boundary.
example {w : ℕ} {d : DTPairsArgs} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hsafe : dtFillAllPairsProgSafe w d s) :
    Memory.FramedTriple w s (dtFillAllPairsProg d) (d.numV * (1 + 2 * d.numV))
      (Set.Ico d.arrA (d.arrA + d.numV.choose 2) ∪
        Set.Ico d.arrB (d.arrB + d.numV.choose 2))
      (fun res s' =>
        res = d.numV.choose 2 ∧ s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        ∀ k (hk : k < d.numV.choose 2),
          s'.mem (d.arrA + k) =
            ((allPairs d.numV)[k]'(by rw [length_allPairs]; exact hk)).1.val ∧
          s'.mem (d.arrB + k) =
            ((allPairs d.numV)[k]'(by rw [length_allPairs]; exact hk)).2.val) ∧
    Realizes .exact dtFillAllPairsProg dtPairsArgsWords WordEncoding.encode
      dtFillAllPairsProgSafe (fun _ _ => 0) :=
  ⟨dtFillAllPairsProg_spec hwf hsafe, realizes_dtFillAllPairsProg⟩

example :
    let s0 : Memory.State := ⟨fun _ => 0, 0⟩
    let d0 : DTPairsArgs := ⟨0, 0, 0⟩
    Memory.FramedTriple 16 s0 (dtFillAllPairsProg d0) 0 ∅
      fun res s' => res = 0 ∧ s'.frontier = 0 ∧ Memory.WellFormed 16 s' := by
  intro s0 d0
  have hwf0 : Memory.WellFormed 16 s0 := ⟨Nat.two_pow_pos 16, fun _ => Nat.two_pow_pos 16⟩
  have hsafe0 : dtFillAllPairsProgSafe 16 d0 s0 :=
    (dtFillAllPairsProgSafe_iff 16 d0 s0).mpr
      ⟨by decide, by decide, by decide, fun h => by omega, by simp [d0, s0],
       by simp [d0, s0], Or.inl (by simp [d0])⟩
  have hft := dtFillAllPairsProg_spec hwf0 hsafe0
  simpa [d0, s0] using hft.mono le_rfl fun res s' ⟨hres, hfr, hwf', _⟩ => ⟨hres, hfr, hwf'⟩

-- `dtFillPowProg_spec`, `realizes_dtFillPowProg`, and `len = 0` boundary.
example {w : ℕ} {d : DTPowArgs} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hsafe : dtFillPowProgSafe w d s) :
    Memory.FramedTriple w s (dtFillPowProg d) (1 + 2 * d.len)
      (Set.Ico d.powArr (d.powArr + d.len + 1))
      (fun res s' =>
        res = d.len ∧ s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        ∀ k ≤ d.len, s'.mem (d.powArr + k) = d.base ^ k) ∧
    Realizes .exact dtFillPowProg dtPowArgsWords WordEncoding.encode
      dtFillPowProgSafe (fun _ _ => 0) :=
  ⟨dtFillPowProg_spec hwf hsafe, realizes_dtFillPowProg⟩

example :
    let s0 : Memory.State := ⟨fun _ => 0, 1⟩
    let d0 : DTPowArgs := ⟨0, 3, 0⟩
    Memory.FramedTriple 16 s0 (dtFillPowProg d0) 1 (Set.Ico 0 1)
      fun res s' => res = 0 ∧ s'.frontier = 1 ∧ s'.mem 0 = 1 := by
  intro s0 d0
  have hwf0 : Memory.WellFormed 16 s0 := ⟨by decide, fun _ => Nat.two_pow_pos 16⟩
  have hsafe0 : dtFillPowProgSafe 16 d0 s0 :=
    (dtFillPowProgSafe_iff 16 d0 s0).mpr
      ⟨by decide, by decide, by decide, by decide, by simp [d0, s0]⟩
  have hft := dtFillPowProg_spec hwf0 hsafe0
  refine hft.mono (by decide) fun res s' ⟨hres, hfr, _, hpow⟩ =>
    ⟨hres, hfr, by simpa [d0] using hpow 0 le_rfl⟩

-- `dtDecodeMaskProg_spec` + `realizes_dtDecodeMaskProg` (general and empty `r0 = 0` witness).
example {w r0 : ℕ} {d : DTDecodeMaskArgs} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hsafe : dtDecodeMaskProgSafe w d s)
    (hmaxE : d.maxE = r0.choose 2)
    (hpairs : ∀ k (hk : k < r0.choose 2),
      s.mem (d.r0PairA + k) = ((allPairs r0)[k]'(by rw [length_allPairs]; exact hk)).1.val ∧
      s.mem (d.r0PairB + k) = ((allPairs r0)[k]'(by rw [length_allPairs]; exact hk)).2.val)
    (hduv : d.edgeU + r0.choose 2 ≤ d.edgeV ∨ d.edgeV + r0.choose 2 ≤ d.edgeU)
    (hdup : d.edgeU + r0.choose 2 ≤ d.edgePair ∨ d.edgePair + r0.choose 2 ≤ d.edgeU)
    (hdvp : d.edgeV + r0.choose 2 ≤ d.edgePair ∨ d.edgePair + r0.choose 2 ≤ d.edgeV)
    (hdua : d.edgeU + r0.choose 2 ≤ d.r0PairA ∨ d.r0PairA + r0.choose 2 ≤ d.edgeU)
    (hdub : d.edgeU + r0.choose 2 ≤ d.r0PairB ∨ d.r0PairB + r0.choose 2 ≤ d.edgeU)
    (hdva : d.edgeV + r0.choose 2 ≤ d.r0PairA ∨ d.r0PairA + r0.choose 2 ≤ d.edgeV)
    (hdvb : d.edgeV + r0.choose 2 ≤ d.r0PairB ∨ d.r0PairB + r0.choose 2 ≤ d.edgeV)
    (hdpa : d.edgePair + r0.choose 2 ≤ d.r0PairA ∨ d.r0PairA + r0.choose 2 ≤ d.edgePair)
    (hdpb : d.edgePair + r0.choose 2 ≤ d.r0PairB ∨ d.r0PairB + r0.choose 2 ≤ d.edgePair) :
    Memory.FramedTriple w s (dtDecodeMaskProg d) (5 * d.maxE)
      (Set.Ico d.edgeU (d.edgeU + d.maxE) ∪ Set.Ico d.edgeV (d.edgeV + d.maxE) ∪
        Set.Ico d.edgePair (d.edgePair + d.maxE))
      (fun res s' =>
        res = (maskEdgePairs r0 d.mask).length ∧
        s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        ∀ j (hj : j < (maskEdgePairs r0 d.mask).length),
          s'.mem (d.edgeU + j) = ((maskEdgePairs r0 d.mask)[j]).1.val ∧
          s'.mem (d.edgeV + j) = ((maskEdgePairs r0 d.mask)[j]).2.val ∧
          s'.mem (d.edgePair + j) =
            pairIdx ((maskEdgePairs r0 d.mask)[j]).1.val
              ((maskEdgePairs r0 d.mask)[j]).2.val) ∧
    Realizes .exact dtDecodeMaskProg dtDecodeMaskArgsWords WordEncoding.encode
      dtDecodeMaskProgSafe (fun _ _ => 0) :=
  ⟨dtDecodeMaskProg_spec hwf hsafe hmaxE hpairs hduv hdup hdvp hdua hdub hdva hdvb hdpa hdpb,
   realizes_dtDecodeMaskProg⟩

example :
    let s0 : Memory.State := ⟨fun _ => 0, 0⟩
    let d0 : DTDecodeMaskArgs := ⟨0, 0, 0, 0, 0, 0, 0⟩
    Memory.FramedTriple 16 s0 (dtDecodeMaskProg d0) 0 ∅
      fun res s' => res = 0 ∧ s'.frontier = 0 := by
  intro s0 d0
  have hwf0 : Memory.WellFormed 16 s0 := ⟨Nat.two_pow_pos 16, fun _ => Nat.two_pow_pos 16⟩
  have hsafe0 : dtDecodeMaskProgSafe 16 d0 s0 :=
    (dtDecodeMaskProgSafe_iff 16 d0 s0).mpr
      ⟨by decide, by decide, by simp [d0, s0], by simp [d0, s0],
       by simp [d0, s0], by simp [d0, s0], by simp [d0, s0]⟩
  have hft := dtDecodeMaskProg_spec (r0 := 0) hwf0 hsafe0 rfl
    (fun k hk => absurd hk (Nat.not_lt_zero _))
    (Or.inl le_rfl) (Or.inl le_rfl) (Or.inl le_rfl)
    (Or.inl le_rfl) (Or.inl le_rfl) (Or.inl le_rfl)
    (Or.inl le_rfl) (Or.inl le_rfl) (Or.inl le_rfl)
  simpa [d0] using hft.mono (by decide) fun res s' ⟨hres, hfr, _, _⟩ =>
    ⟨hres.trans (by simp [d0, maskEdgePairs]), hfr⟩

-- `dtKruskalMaskProg_spec`, `realizes_dtKruskalMaskProg`, and `e = 0` boundary witness.
example {w : ℕ} {d : DTKruskalProgArgs} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hsafe : dtKruskalMaskProgSafe w d s)
    (p : Equiv.Perm (Fin d.e))
    (hord : ∀ rk (hrk : rk < d.e), s.mem (d.orderArr + rk) = (p.symm ⟨rk, hrk⟩).val)
    (ends : Fin d.e → Sym2 (Fin d.r0))
    (hends : ∀ i : Fin d.e, ∃ a b : Fin d.r0, ends i = s(a, b) ∧
      s.mem (d.edgeU + i.val) = a.val ∧ s.mem (d.edgeV + i.val) = b.val) :
    Memory.FramedTriple w s (dtKruskalMaskProg d) (d.r0 + d.e * (5 + 2 * d.r0))
      (Set.Ico d.compArr (d.compArr + d.r0))
      (fun res s' =>
        res = maskOfFinset (Cslib.Multigraph.msf ends p Finset.univ) ∧
        s'.frontier = s.frontier ∧ Memory.WellFormed w s') ∧
    Realizes .exact dtKruskalMaskProg dtKruskalProgArgsWords WordEncoding.encode
      dtKruskalMaskProgSafe (fun _ _ => 0) :=
  ⟨dtKruskalMaskProg_spec hwf hsafe p hord ends hends, realizes_dtKruskalMaskProg⟩

example :
    let s0 : Memory.State := ⟨fun _ => 0, 3⟩
    let d0 : DTKruskalProgArgs := ⟨3, 0, 0, 0, 0, 0⟩
    Memory.FramedTriple 16 s0 (dtKruskalMaskProg d0) 3 (Set.Ico 0 3)
      fun res s' =>
        res = maskOfFinset
          (Cslib.Multigraph.msf (fun i : Fin 0 => (Fin.elim0 i : Sym2 (Fin 3)))
            (Equiv.refl (Fin 0)) Finset.univ) ∧
        s'.frontier = 3 := by
  intro s0 d0
  have hwf0 : Memory.WellFormed 16 s0 := ⟨by decide, fun _ => Nat.two_pow_pos 16⟩
  have hsafe0 : dtKruskalMaskProgSafe 16 d0 s0 :=
    (dtKruskalMaskProgSafe_iff 16 d0 s0).mpr
      ⟨by decide, by decide, by decide, by decide,
       by simp [d0, s0], by simp [d0, s0], by simp [d0, s0], by simp [d0, s0],
       Or.inr (by simp [d0]), Or.inr (by simp [d0]), Or.inr (by simp [d0]),
       fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hft := dtKruskalMaskProg_spec hwf0 hsafe0 (Equiv.refl (Fin 0))
    (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun i : Fin 0 => (Fin.elim0 i : Sym2 (Fin 3))) (fun i => Fin.elim0 i)
  exact hft.mono (by simp [d0]) fun res s' ⟨hres, hfr, _⟩ => ⟨hres, hfr⟩

/-! ## Non-empty Checked Witnesses (`numV = 3` and Multigraph `r0 = 4, e = 4`) -/

-- Non-empty `numV = 3` witness for `dtFillAllPairsProg_spec` enumerating all pairs of `Fin 3`.
example :
    let s0 : Memory.State := ⟨fun _ => 0, 10⟩
    let d3 : DTPairsArgs := ⟨0, 3, 3⟩
    Memory.FramedTriple 16 s0 (dtFillAllPairsProg d3) 21 (Set.Ico 0 3 ∪ Set.Ico 3 6)
      fun res s' =>
        res = 3 ∧ s'.frontier = 10 ∧
        s'.mem 0 = 0 ∧ s'.mem 3 = 1 ∧
        s'.mem 1 = 0 ∧ s'.mem 4 = 2 ∧
        s'.mem 2 = 1 ∧ s'.mem 5 = 2 := by
  intro s0 d3
  have hwf0 : Memory.WellFormed 16 s0 := ⟨by decide, fun _ => Nat.two_pow_pos 16⟩
  have hsafe0 : dtFillAllPairsProgSafe 16 d3 s0 :=
    (dtFillAllPairsProgSafe_iff 16 d3 s0).mpr
      ⟨by decide, by decide, by decide, fun _ => by decide,
       by decide, by decide, Or.inl (by decide)⟩
  refine (dtFillAllPairsProg_spec hwf0 hsafe0).mono (by decide)
    fun res s' ⟨hres, hfr, _, hvals⟩ => ?_
  have h0 := hvals 0 (by decide)
  have h1 := hvals 1 (by decide)
  have h2 := hvals 2 (by decide)
  dsimp only [d3] at hres h0 h1 h2
  exact ⟨hres, hfr, h0.1.trans rfl, h0.2.trans rfl, h1.1.trans rfl, h1.2.trans rfl,
    h2.1.trans rfl, h2.2.trans rfl⟩

private def pairs3Mem (a : ℕ) : ℕ :=
  if a = 2 ∨ a = 3 then 1 else if a = 4 ∨ a = 5 then 2 else 0

private theorem maskEdgePairs_3_5 :
    maskEdgePairs 3 5 = [(⟨0, by decide⟩, ⟨1, by decide⟩), (⟨1, by decide⟩, ⟨2, by decide⟩)] := rfl

-- Non-empty `r0 = 3, mask = 5` witness for `dtDecodeMaskProg_spec` decoding `(0, 1)` and `(1, 2)`.
example :
    let s0 : Memory.State := ⟨pairs3Mem, 15⟩
    let d3 : DTDecodeMaskArgs := ⟨0, 3, 6, 9, 12, 5, 3⟩
    Memory.FramedTriple 16 s0 (dtDecodeMaskProg d3) 15
      (Set.Ico 6 9 ∪ Set.Ico 9 12 ∪ Set.Ico 12 15)
      fun res s' =>
        res = 2 ∧ s'.frontier = 15 ∧
        s'.mem 6 = 0 ∧ s'.mem 9 = 1 ∧ s'.mem 12 = 0 ∧
        s'.mem 7 = 1 ∧ s'.mem 10 = 2 ∧ s'.mem 13 = 2 := by
  intro s0 d3
  have hwf0 : Memory.WellFormed 16 s0 := ⟨by decide, fun a => by
    dsimp only [s0, pairs3Mem]; split_ifs <;> decide⟩
  have hsafe0 : dtDecodeMaskProgSafe 16 d3 s0 :=
    (dtDecodeMaskProgSafe_iff 16 d3 s0).mpr
      ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  have hpairs : ∀ k (hk : k < Nat.choose 3 2),
      s0.mem (d3.r0PairA + k) = ((allPairs 3)[k]'(by rw [length_allPairs]; exact hk)).1.val ∧
      s0.mem (d3.r0PairB + k) = ((allPairs 3)[k]'(by rw [length_allPairs]; exact hk)).2.val := by
    intro k hk
    have hk' : k < 3 := by simpa using hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
  have hft := dtDecodeMaskProg_spec (r0 := 3) hwf0 hsafe0 rfl hpairs
    (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
    (Or.inr (by decide)) (Or.inr (by decide)) (Or.inr (by decide))
    (Or.inr (by decide)) (Or.inr (by decide)) (Or.inr (by decide))
  refine hft.mono (by decide) fun res s' ⟨hres, hfr, _, hedges⟩ => ?_
  have hlen : (maskEdgePairs 3 5).length = 2 := rfl
  have h0 := hedges 0 (by rw [hlen]; decide)
  have h1 := hedges 1 (by rw [hlen]; decide)
  dsimp only [d3] at hres h0 h1
  simp only [maskEdgePairs_3_5] at h0 h1
  exact ⟨hres.trans hlen, hfr, h0.1, h0.2.1,
    h0.2.2.trans (show pairIdx 0 1 = 0 from rfl),
    h1.1, h1.2.1, h1.2.2.trans (show pairIdx 1 2 = 2 from rfl)⟩

private def kruskalMultiMem : ℕ → ℕ
  | 3 | 5 | 6 | 11 => 1
  | 7 | 8 => 2
  | 9 => 3
  | _ => 0

private def kruskalMultiEnds (i : Fin 4) : Sym2 (Fin 4) :=
  match i.val with
  | 0 => s(⟨0, by decide⟩, ⟨0, by decide⟩)
  | 1 => s(⟨0, by decide⟩, ⟨1, by decide⟩)
  | 2 => s(⟨0, by decide⟩, ⟨1, by decide⟩)
  | _ => s(⟨1, by decide⟩, ⟨2, by decide⟩)

private def kruskalMultiPerm : Equiv.Perm (Fin 4) :=
  (Equiv.swap ⟨0, by decide⟩ ⟨2, by decide⟩).trans (Equiv.swap ⟨1, by decide⟩ ⟨3, by decide⟩)

-- Non-empty multigraph witness (`r0 = 4, e = 4`) for `dtKruskalMaskProg_spec` with self-loop `0`,
-- parallel edges `1, 2` (weights ordered `2 < 3 < 0 < 1`), bridge `3`, and isolated vertex `3`.
example :
    let s0 : Memory.State := ⟨kruskalMultiMem, 16⟩
    let d4 : DTKruskalProgArgs := ⟨4, 4, 0, 4, 8, 12⟩
    Memory.FramedTriple 16 s0 (dtKruskalMaskProg d4) (4 + 4 * (5 + 2 * 4)) (Set.Ico 12 16)
      fun res s' =>
        res = maskOfFinset (Cslib.Multigraph.msf kruskalMultiEnds kruskalMultiPerm Finset.univ) ∧
        res = 12 ∧ s'.frontier = 16 := by
  intro s0 d4
  have hwf0 : Memory.WellFormed 16 s0 :=
    ⟨by decide, fun a => by dsimp only [s0]; unfold kruskalMultiMem; split <;> decide⟩
  have hord : ∀ rk (hrk : rk < 4),
      s0.mem (d4.orderArr + rk) = (kruskalMultiPerm.symm ⟨rk, hrk⟩).val := by
    intro rk hrk
    rcases (by omega : rk = 0 ∨ rk = 1 ∨ rk = 2 ∨ rk = 3) with rfl | rfl | rfl | rfl <;>
      simp [s0, d4, kruskalMultiMem, kruskalMultiPerm, Equiv.swap_apply_def]
  have hsafe0 : dtKruskalMaskProgSafe 16 d4 s0 := by
    refine (dtKruskalMaskProgSafe_iff 16 d4 s0).mpr
      ⟨by decide, by decide, by decide, by decide,
       by decide, by decide, by decide, by decide,
       Or.inr (by decide), Or.inr (by decide), Or.inr (by decide),
       fun rk hrk => by rw [hord rk hrk]; exact (kruskalMultiPerm.symm ⟨rk, hrk⟩).isLt,
       fun i hi => ?_⟩
    dsimp only [d4] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
      simp [s0, d4, kruskalMultiMem]
  have hends : ∀ i : Fin 4, ∃ a b : Fin 4, kruskalMultiEnds i = s(a, b) ∧
      s0.mem (d4.edgeU + i.val) = a.val ∧ s0.mem (d4.edgeV + i.val) = b.val := by
    intro i
    rcases i with ⟨i, hi⟩
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · exact ⟨⟨0, by decide⟩, ⟨0, by decide⟩, rfl, rfl, rfl⟩
    · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, rfl, rfl, rfl⟩
    · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, rfl, rfl, rfl⟩
    · exact ⟨⟨1, by decide⟩, ⟨2, by decide⟩, rfl, rfl, rfl⟩
  have hp0 : kruskalMultiPerm ⟨0, by decide⟩ = ⟨2, by decide⟩ := by
    simp [kruskalMultiPerm, Equiv.swap_apply_def]
  have hp1 : kruskalMultiPerm ⟨1, by decide⟩ = ⟨3, by decide⟩ := by
    simp [kruskalMultiPerm, Equiv.swap_apply_def]
  have hp2 : kruskalMultiPerm ⟨2, by decide⟩ = ⟨0, by decide⟩ := by
    simp [kruskalMultiPerm, Equiv.swap_apply_def]
  have hp3 : kruskalMultiPerm ⟨3, by decide⟩ = ⟨1, by decide⟩ := by
    simp [kruskalMultiPerm, Equiv.swap_apply_def]
  have hmsf : Cslib.Multigraph.msf kruskalMultiEnds kruskalMultiPerm Finset.univ =
      ({⟨2, by decide⟩, ⟨3, by decide⟩} : Finset (Fin 4)) := by
    ext i
    simp only [Finset.mem_insert, Finset.mem_singleton]
    have hj0 : Cslib.Multigraph.Joins kruskalMultiEnds
        {e | e ∈ (Finset.univ : Finset (Fin 4)) ∧
          kruskalMultiPerm e < kruskalMultiPerm ⟨0, by decide⟩}
        ⟨0, by decide⟩ ⟨0, by decide⟩ := Cslib.Multigraph.Joins.refl _
    have hj1 : Cslib.Multigraph.Joins kruskalMultiEnds
        {e | e ∈ (Finset.univ : Finset (Fin 4)) ∧
          kruskalMultiPerm e < kruskalMultiPerm ⟨1, by decide⟩}
        ⟨0, by decide⟩ ⟨1, by decide⟩ :=
      Cslib.Multigraph.Joins.of_mem (e := ⟨2, by decide⟩)
        ⟨Finset.mem_univ _, by rw [hp1, hp2]; decide⟩ rfl
    have hj2 : ¬ Cslib.Multigraph.Joins kruskalMultiEnds
        {e | e ∈ (Finset.univ : Finset (Fin 4)) ∧
          kruskalMultiPerm e < kruskalMultiPerm ⟨2, by decide⟩}
        ⟨0, by decide⟩ ⟨1, by decide⟩ := by
      have hempty : {e | e ∈ (Finset.univ : Finset (Fin 4)) ∧
          kruskalMultiPerm e < kruskalMultiPerm ⟨2, by decide⟩} = ∅ := by
        ext e
        simp only [Set.mem_ofPred_eq, Finset.mem_univ, true_and, Set.mem_empty_iff_false,
          iff_false, hp2]
        exact fun h => Nat.not_lt_zero _ h
      rw [hempty, Cslib.Multigraph.joins_empty_iff]
      decide
    have hj3 : ¬ Cslib.Multigraph.Joins kruskalMultiEnds
        {e | e ∈ (Finset.univ : Finset (Fin 4)) ∧
          kruskalMultiPerm e < kruskalMultiPerm ⟨3, by decide⟩}
        ⟨1, by decide⟩ ⟨2, by decide⟩ := by
      intro hjoin
      have hl := hjoin.lift (ends' := fun _ : Empty => s(0, 0)) (T := ∅)
        (fun v => if v.val ≤ 1 then (0 : ℕ) else 1) fun e he a b hab => by
          have he2 : e = ⟨2, by decide⟩ := by
            rcases he with ⟨_, hlt⟩
            rcases e with ⟨e, he_lt⟩
            rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with rfl | rfl | rfl | rfl
            · rw [hp0, hp3] at hlt; exact absurd hlt (by decide)
            · rw [hp1, hp3] at hlt; exact absurd hlt (by decide)
            · rfl
            · exact absurd hlt (lt_irrefl _)
          subst he2
          have h2eq : s(⟨0, by decide⟩, ⟨1, by decide⟩) = s(a, b) := hab
          rcases Sym2.eq_iff.mp h2eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            exact Cslib.Multigraph.Joins.refl _
      have heq := Cslib.Multigraph.joins_empty_iff.mp hl
      simp at heq
    rcases i with ⟨i, hi⟩
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · rw [Cslib.Multigraph.mem_msf_iff kruskalMultiPerm
        (rfl : kruskalMultiEnds ⟨0, by decide⟩ = s(⟨0, by decide⟩, ⟨0, by decide⟩))]
      exact iff_of_false (fun h => h.2 hj0) (by simp)
    · rw [Cslib.Multigraph.mem_msf_iff kruskalMultiPerm
        (rfl : kruskalMultiEnds ⟨1, by decide⟩ = s(⟨0, by decide⟩, ⟨1, by decide⟩))]
      exact iff_of_false (fun h => h.2 hj1) (by simp)
    · rw [Cslib.Multigraph.mem_msf_iff kruskalMultiPerm
        (rfl : kruskalMultiEnds ⟨2, by decide⟩ = s(⟨0, by decide⟩, ⟨1, by decide⟩))]
      exact iff_of_true ⟨Finset.mem_univ _, by simpa [Finset.mem_univ] using hj2⟩ (by simp)
    · rw [Cslib.Multigraph.mem_msf_iff kruskalMultiPerm
        (rfl : kruskalMultiEnds ⟨3, by decide⟩ = s(⟨1, by decide⟩, ⟨2, by decide⟩))]
      exact iff_of_true ⟨Finset.mem_univ _, by simpa [Finset.mem_univ] using hj3⟩ (by simp)
  have hmask : maskOfFinset
      (Cslib.Multigraph.msf kruskalMultiEnds kruskalMultiPerm Finset.univ) = 12 := by
    rw [hmsf]; simp [maskOfFinset]
  have hft := dtKruskalMaskProg_spec hwf0 hsafe0 kruskalMultiPerm hord kruskalMultiEnds hends
  refine hft.mono (by simp [d4]) fun res s' ⟨hres, hfr, _⟩ => ⟨hres, hres.trans hmask, hfr⟩

end CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.DecisionTreeLayout
