/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.IndexedEdges
public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Contraction.Robust
import CslibFrontier.Algorithms.WordRAM.CountingSort
import CslibFrontier.Computability.WordRAM.Realization.LoopFrame
import CslibFrontier.Computability.WordRAM.Realization.RecordOps
import CslibFrontier.Foundations.Data.List.Subperm
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.ValidProg

/-!
# Edge deduplication on WordRAM

Linear-time WordRAM edge normalization and deduplication over stride-4 `IndexedEdge` arrays
(`GraphSlice`), realizing `dedupSimpleEdges` in `O(m + n)` memory operations.

## Main definitions

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.dedupSimpleEdgesProg`: self-loop filter,
  stable two-pass `countingSortProg`, and min scan.

## Main results

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_dedupSimpleEdgesProg`,
  `dedupSimpleEdgesProg_spec`: `Realizes .exact` and `O(m + n)` framed specification matching
  `dedupSimpleEdges`.
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization
open Cslib.Algorithms.Lean.Kruskal (WeightedEdge)
open Cslib.Query.MinimumSpanningForest
open Cslib.Algorithms.WordRAM
  (CountingSortArgs countingSortArgsWords countingSortPure countingSortPure_perm
    countingSortPure_stable countingSortProg countingSortProg_spec realizes_countingSortProg)

/-! ## Single-edge copy helper -/

/-- Arguments for copying one stride-4 `IndexedEdge` record from `srcBase + 4 * srcIdx` to
`dstBase + 4 * dstIdx`. -/
private structure CopyIndexedEdgeArgs where
  /-- Base address of the source `IndexedEdge` array. -/
  srcBase : ℕ
  /-- Base address of the destination `IndexedEdge` array. -/
  dstBase : ℕ
  /-- Source edge ordinal inside `srcBase`. -/
  srcIdx : ℕ
  /-- Destination edge ordinal inside `dstBase`. -/
  dstIdx : ℕ

/-- Four-word encoding of `CopyIndexedEdgeArgs` as `(srcBase, dstBase, srcIdx, dstIdx)`. -/
private word_enc_structure encCopyIndexedEdgeArgs : CopyIndexedEdgeArgs where
  srcBase : wordWords,
  dstBase : wordWords,
  srcIdx : wordWords,
  dstIdx : wordWords

/-- Word encoding instance for `CopyIndexedEdgeArgs`. -/
private instance : WordEncoding CopyIndexedEdgeArgs := ⟨4, encCopyIndexedEdgeArgs⟩

/-- Copy one stride-4 `IndexedEdge` from `a.srcBase + 4 * a.srcIdx` to
`a.dstBase + 4 * a.dstIdx` via `Memory.copy`. -/
private def copyIndexedEdge (a : CopyIndexedEdgeArgs) : Memory.Prog Unit :=
  Memory.copy (a.srcBase + 4 * a.srcIdx) (a.dstBase + 4 * a.dstIdx) 4

/-- Uniform `Realizes .exact` certificate for `copyIndexedEdge` with `work = 0`. -/
private theorem realizes_copyIndexedEdge : Realizes .exact copyIndexedEdge
    encCopyIndexedEdgeArgs WordEncoding.encode
    (fun w a s => Fits w 16 ∧ a.srcBase + 4 * a.srcIdx + 4 ≤ s.frontier ∧
      a.dstBase + 4 * a.dstIdx + 4 ≤ s.frontier)
    (fun _ _ => 0) := by
  unfold copyIndexedEdge
  realize [realizes_copy]
  all_goals
    rcases h with ⟨h16, hsrc, hdst⟩
    have hfront := hmem.frontier_fits
    first | exact hsrc | exact hdst | fits

/-- Framed specification of `copyIndexedEdge`: copies one stride-4 edge from
`srcBase + 4 * srcIdx` to `dstBase + 4 * dstIdx` in at most `8` memory operations,
modifying only `[dstBase + 4 * dstIdx, dstBase + 4 * dstIdx + 4)`. -/
private theorem copyIndexedEdge_spec {w srcBase dstBase srcIdx dstIdx : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hsrc : srcBase + 4 * srcIdx + 4 ≤ s.frontier)
    (hdst : dstBase + 4 * dstIdx + 4 ≤ s.frontier)
    (hdisj : srcBase + 4 * srcIdx + 4 ≤ dstBase + 4 * dstIdx ∨
      dstBase + 4 * dstIdx + 4 ≤ srcBase + 4 * srcIdx) :
    Memory.FramedTriple w s (copyIndexedEdge ⟨srcBase, dstBase, srcIdx, dstIdx⟩) 8
      (Set.Ico (dstBase + 4 * dstIdx) (dstBase + 4 * dstIdx + 4)) fun _ s' =>
        s'.frontier = s.frontier ∧
        Memory.WellFormed w s' ∧
        ∀ q < 4, s'.mem (dstBase + 4 * dstIdx + q) = s.mem (srcBase + 4 * srcIdx + q) := by
  have hcopy := (Memory.FramedTriple.copy hdisj hsrc hdst (fun _ _ => hwf.mem_fits _)
    (Q := fun _ t => t.frontier = s.frontier ∧
      ∀ q < 4, t.mem (dstBase + 4 * dstIdx + q) = s.mem (srcBase + 4 * srcIdx + q))
    ⟨rfl, fun q hq => ArrayCopy.copyPrefix_read hq⟩).wellFormed hwf
  exact hcopy.mono (by decide) fun _ _ ⟨⟨hfr, hmem⟩, hwf'⟩ => ⟨hfr, hwf', hmem⟩

private theorem holdsRecords_zero_mem {base : ℕ} {rows : List (Fin 3 → ℕ)} {mem : ℕ → ℕ}
    (hrows : HoldsRecords 3 base rows mem) (hk : 0 < rows.length) :
    mem base = rows[0] 0 ∧ mem (base + 1) = rows[0] 1 ∧ mem (base + 2) = rows[0] 2 :=
  ⟨by simpa using hrows 0 hk ⟨0, by decide⟩,
   by simpa using hrows 0 hk ⟨1, by decide⟩,
   by simpa using hrows 0 hk ⟨2, by decide⟩⟩

/-! ## Pure canonical-pair order and `dedupSimpleEdges` correspondence -/

private def edgePairNat {n : ℕ} (e : IndexedEdge n) : ℕ × ℕ :=
  if e.u.val < e.v.val then (e.u.val, e.v.val) else (e.v.val, e.u.val)

private def weightedPairNat {n : ℕ} (e : WeightedEdge n ℕ) : ℕ × ℕ :=
  if e.u.val < e.v.val then (e.u.val, e.v.val) else (e.v.val, e.u.val)

private theorem sym2_eq_iff_edgePairNat_eq {n : ℕ} {e₁ e₂ : IndexedEdge n} :
    s(e₁.u, e₁.v) = s(e₂.u, e₂.v) ↔ edgePairNat e₁ = edgePairNat e₂ := by
  simp only [Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff, edgePairNat]
  constructor <;> [rintro (⟨h1, h2⟩ | ⟨h1, h2⟩); intro h] <;> split_ifs at * <;> omega

private def pairOrderLT (p₁ p₂ : ℕ × ℕ) : Prop :=
  p₁.2 < p₂.2 ∨ (p₁.2 = p₂.2 ∧ p₁.1 < p₂.1)

private theorem pairOrderLT_irrefl (p : ℕ × ℕ) : ¬pairOrderLT p p := by
  dsimp only [pairOrderLT]; omega

private theorem pairOrderLT_trans {a b c : ℕ × ℕ}
    (hab : pairOrderLT a b) (hbc : pairOrderLT b c) : pairOrderLT a c := by
  dsimp only [pairOrderLT] at hab hbc ⊢; omega

private theorem pairOrderLT_asymm {a b : ℕ × ℕ} (hab : pairOrderLT a b) (hba : pairOrderLT b a) :
    False := pairOrderLT_irrefl a (pairOrderLT_trans hab hba)

private def pairIdxLT (r₁ r₂ : Fin 3 → ℕ) : Prop :=
  pairOrderLT (r₁ 0, r₁ 1) (r₂ 0, r₂ 1) ∨ ((r₁ 0, r₁ 1) = (r₂ 0, r₂ 1) ∧ r₁ 2 < r₂ 2)

private def edgeRow {n : ℕ} (e : IndexedEdge n) (i : ℕ) : Fin 3 → ℕ :=
  ![(edgePairNat e).1, (edgePairNat e).2, i]

private def prepRows {n : ℕ} (es : List (IndexedEdge n)) (k : ℕ) : List (Fin 3 → ℕ) :=
  ((List.finRange es.length).take k).filterMap fun i =>
    if es[i.val].u = es[i.val].v then none else some (edgeRow es[i.val] i.val)

private theorem prepRows_succ {n : ℕ} (es : List (IndexedEdge n)) {k : ℕ} (hk : k < es.length) :
    prepRows es (k + 1) = prepRows es k ++
      (if es[k].u = es[k].v then [] else [edgeRow es[k] k]) := by
  dsimp only [prepRows]
  have htake : (List.finRange es.length).take (k + 1) =
      (List.finRange es.length).take k ++ [⟨k, hk⟩] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by simp [hk]), Option.toList_some]; simp
  rw [htake, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  split_ifs <;> simp

private theorem prepRows_length_le {n : ℕ} (es : List (IndexedEdge n)) (k : ℕ) :
    (prepRows es k).length ≤ k := by
  have h1 : (prepRows es k).length ≤ ((List.finRange es.length).take k).length :=
    List.length_filterMap_le _ _
  simp only [List.length_take, List.length_finRange] at h1; omega

private theorem prepRows_pairwise_idx {n : ℕ} (es : List (IndexedEdge n)) :
    (prepRows es es.length).Pairwise (fun r₁ r₂ => r₁ 2 < r₂ 2) := by
  dsimp only [prepRows]; rw [List.take_of_length_le (by simp)]
  refine (show (List.finRange es.length).Pairwise (fun a b : Fin es.length => a.val < b.val) from
    List.pairwise_iff_getElem.mpr fun _ _ _ _ h => by simpa using h).filterMap _
      fun _ _ hij r₁ hr₁ r₂ hr₂ => ?_
  split_ifs at hr₁ hr₂; cases hr₁; cases hr₂; exact hij

private theorem prepRows_mem {n : ℕ} {es : List (IndexedEdge n)} {r : Fin 3 → ℕ}
    (hr : r ∈ prepRows es es.length) :
    ∃ hlt : r 2 < es.length, es[r 2].u ≠ es[r 2].v ∧
      edgePairNat es[r 2] = (r 0, r 1) ∧ r 0 < r 1 ∧ r 0 < n ∧ r 1 < n := by
  dsimp only [prepRows] at hr
  rw [List.take_of_length_le (by simp), List.mem_filterMap] at hr
  obtain ⟨i, _, hfi⟩ := hr; split_ifs at hfi with heq; cases hfi
  have hu := es[i.val].u.isLt; have hv := es[i.val].v.isLt
  have hne : es[i.val].u.val ≠ es[i.val].v.val := fun h => heq (Fin.ext h)
  refine ⟨i.isLt, heq, rfl, ?_⟩
  change (edgePairNat es[i.val]).1 < (edgePairNat es[i.val]).2 ∧
    (edgePairNat es[i.val]).1 < n ∧ (edgePairNat es[i.val]).2 < n
  dsimp only [edgePairNat]; split_ifs <;> omega

private theorem mem_prepRows_of_ne {n : ℕ} {es : List (IndexedEdge n)}
    (i : Fin es.length) (hne : es[i.val].u ≠ es[i.val].v) :
    edgeRow es[i.val] i.val ∈ prepRows es es.length := by
  dsimp only [prepRows]; rw [List.take_of_length_le (by simp), List.mem_filterMap]
  exact ⟨i, List.mem_finRange i, by simp [hne]⟩

private def IsPairMin {n : ℕ} (es : List (IndexedEdge n)) (p : ℕ × ℕ) (q : Fin es.length) : Prop :=
  es[q.val].u ≠ es[q.val].v ∧ edgePairNat es[q.val] = p ∧
  ∀ i : Fin es.length, es[i.val].u ≠ es[i.val].v → edgePairNat es[i.val] = p →
    es[q.val].weight < es[i.val].weight ∨ (es[q.val].weight = es[i.val].weight ∧ q.val ≤ i.val)

private theorem isPairMin_unique {n : ℕ} {es : List (IndexedEdge n)} {p : ℕ × ℕ}
    {q₁ q₂ : Fin es.length} (h₁ : IsPairMin es p q₁) (h₂ : IsPairMin es p q₂) : q₁ = q₂ := by
  rcases h₁.2.2 q₂ h₂.1 h₂.2.1 with hlt | ⟨_, hle₁⟩ <;>
    rcases h₂.2.2 q₁ h₁.1 h₁.2.1 with hgt | ⟨_, hle₂⟩ <;> omega

private def minFoldPair {n : ℕ} (p : Fin n × Fin n) (es : List (WeightedEdge n ℕ)) :
    Option (WeightedEdge n ℕ) :=
  es.foldr (fun e tail =>
    if (if e.u.val < e.v.val then (e.u, e.v) else (e.v, e.u)) = p then
      match tail with
      | none => some e
      | some best => some (if e.weight ≤ best.weight then e else best)
    else tail) none

private theorem weighted_match_iff {n : ℕ} {p : Fin n × Fin n} (hp : p.1.val < p.2.val)
    (e : IndexedEdge n) :
    ((if e.toWeighted.u.val < e.toWeighted.v.val then (e.toWeighted.u, e.toWeighted.v)
      else (e.toWeighted.v, e.toWeighted.u)) = p) ↔
      (e.u ≠ e.v ∧ edgePairNat e = (p.1.val, p.2.val)) := by
  dsimp only [edgePairNat, IndexedEdge.toWeighted]
  by_cases hlt : e.u.val < e.v.val <;>
  · simp only [hlt, ↓reduceIte, Prod.ext_iff, Fin.ext_iff, ne_eq]
    exact ⟨fun ⟨h1, h2⟩ => ⟨by omega, h1, h2⟩, fun ⟨_, h1, h2⟩ => ⟨h1, h2⟩⟩

private theorem isPairMin_cons_zero {n : ℕ} {e : IndexedEdge n} {rest : List (IndexedEdge n)}
    {p : ℕ × ℕ} (he : e.u ≠ e.v ∧ edgePairNat e = p)
    (hle : ∀ j' : Fin rest.length, rest[j'.val].u ≠ rest[j'.val].v →
      edgePairNat rest[j'.val] = p → e.weight ≤ rest[j'.val].weight) :
    IsPairMin (e :: rest) p ⟨0, Nat.succ_pos _⟩ := by
  refine ⟨he.1, he.2, fun j hj1 hj2 => ?_⟩
  cases j using Fin.cases with
  | zero => exact .inr ⟨rfl, le_rfl⟩
  | succ j' =>
    rcases Nat.lt_or_eq_of_le (hle j' hj1 hj2) with hlt | heqw
    · exact .inl hlt
    · exact .inr ⟨heqw, Nat.zero_le _⟩

private theorem isPairMin_cons_succ {n : ℕ} {e : IndexedEdge n} {rest : List (IndexedEdge n)}
    {p : ℕ × ℕ} {q' : Fin rest.length} (hq' : IsPairMin rest p q')
    (hhead : ¬(e.u ≠ e.v ∧ edgePairNat e = p) ∨ rest[q'.val].weight < e.weight) :
    IsPairMin (e :: rest) p q'.succ := by
  refine ⟨hq'.1, hq'.2.1, fun j hj1 hj2 => ?_⟩
  cases j using Fin.cases with
  | zero =>
    rcases hhead with hne | hlt
    · exact absurd ⟨hj1, hj2⟩ hne
    · exact .inl hlt
  | succ j' =>
    rcases hq'.2.2 j' hj1 hj2 with hlt | ⟨heqw, hle⟩
    · exact .inl hlt
    · exact .inr ⟨heqw, Nat.succ_le_succ hle⟩

private theorem minFoldPair_eq_none_iff {n : ℕ} {p : Fin n × Fin n} (hp : p.1.val < p.2.val) :
    ∀ es : List (IndexedEdge n),
      minFoldPair p (es.map IndexedEdge.toWeighted) = none ↔
        ∀ i : Fin es.length, ¬(es[i.val].u ≠ es[i.val].v ∧
          edgePairNat es[i.val] = (p.1.val, p.2.val))
  | [] => by simp [minFoldPair]
  | e :: rest => by
    have hrest := minFoldPair_eq_none_iff hp rest
    dsimp only [minFoldPair] at hrest ⊢; rw [List.map_cons, List.foldr_cons]
    by_cases he : e.u ≠ e.v ∧ edgePairNat e = (p.1.val, p.2.val)
    · simp only [(weighted_match_iff hp e).mpr he, ↓reduceIte]
      cases htail : minFoldPair p (rest.map IndexedEdge.toWeighted) <;>
        simp only [minFoldPair] at htail <;> rw [htail] <;>
        exact ⟨fun h => (by cases h), fun hall => absurd he (hall ⟨0, Nat.succ_pos _⟩)⟩
    · have he' : ¬((if e.toWeighted.u.val < e.toWeighted.v.val then
          (e.toWeighted.u, e.toWeighted.v) else (e.toWeighted.v, e.toWeighted.u)) = p) :=
        fun h' => he ((weighted_match_iff hp e).mp h')
      simp only [he', ↓reduceIte, hrest]
      exact ⟨fun hall i => Fin.cases he (fun j => hall j) i, fun hall j => hall j.succ⟩

private theorem minFoldPair_eq_some_iff {n : ℕ} {p : Fin n × Fin n} (hp : p.1.val < p.2.val) :
    ∀ (es : List (IndexedEdge n)) (ew : WeightedEdge n ℕ),
      minFoldPair p (es.map IndexedEdge.toWeighted) = some ew ↔
        ∃ q : Fin es.length, IsPairMin es (p.1.val, p.2.val) q ∧ ew = es[q.val].toWeighted
  | [], ew => by simp [minFoldPair]
  | e :: rest, ew => by
    have hrest := minFoldPair_eq_some_iff hp rest
    have hnone_iff := minFoldPair_eq_none_iff hp rest
    dsimp only [minFoldPair] at hrest hnone_iff ⊢; rw [List.map_cons, List.foldr_cons]
    by_cases he : e.u ≠ e.v ∧ edgePairNat e = (p.1.val, p.2.val)
    · simp only [(weighted_match_iff hp e).mpr he, ↓reduceIte]
      cases htail : minFoldPair p (rest.map IndexedEdge.toWeighted) with
      | none =>
        have hnone := hnone_iff.mp (by simpa [minFoldPair] using htail)
        dsimp only [minFoldPair] at htail; rw [htail]
        have hmin0 := isPairMin_cons_zero he fun j' hj1 hj2 => absurd ⟨hj1, hj2⟩ (hnone j')
        exact ⟨fun h => (by cases h; exact ⟨⟨0, Nat.succ_pos _⟩, hmin0, rfl⟩),
          fun ⟨q, hq, hew⟩ => by rw [hew, isPairMin_unique hq hmin0]; rfl⟩
      | some best =>
        obtain ⟨q', hq', rfl⟩ := (hrest best).mp (by simpa [minFoldPair] using htail)
        dsimp only [minFoldPair] at htail; rw [htail]
        by_cases hw : e.weight ≤ rest[q'.val].weight
        · have hmin := isPairMin_cons_zero he fun j' hj1 hj2 => by
            rcases hq'.2.2 j' hj1 hj2 with h | h <;> omega
          simp only [show e.toWeighted.weight ≤ rest[q'.val].toWeighted.weight from hw, ↓reduceIte]
          exact ⟨fun h => (by cases h; exact ⟨⟨0, Nat.succ_pos _⟩, hmin, rfl⟩),
            fun ⟨q, hq, hew⟩ => by rw [hew, isPairMin_unique hq hmin]; rfl⟩
        · have hmin := isPairMin_cons_succ hq' (.inr (Nat.lt_of_not_le hw))
          simp only [show ¬ e.toWeighted.weight ≤ rest[q'.val].toWeighted.weight from hw,
            ↓reduceIte]
          exact ⟨fun h => (by cases h; exact ⟨q'.succ, hmin, rfl⟩),
            fun ⟨q, hq, hew⟩ => by rw [hew, isPairMin_unique hq hmin]; rfl⟩
    · have he' : ¬((if e.toWeighted.u.val < e.toWeighted.v.val then
          (e.toWeighted.u, e.toWeighted.v) else (e.toWeighted.v, e.toWeighted.u)) = p) :=
        fun h' => he ((weighted_match_iff hp e).mp h')
      simp only [he', ↓reduceIte, hrest]
      refine ⟨fun ⟨q', hq', h⟩ => ⟨q'.succ, isPairMin_cons_succ hq' (.inl he), h⟩,
        fun ⟨q, hq, h⟩ => ?_⟩
      cases q using Fin.cases with
      | zero => exact absurd ⟨hq.1, hq.2.1⟩ he
      | succ q' =>
        refine ⟨q', ⟨hq.1, hq.2.1, fun j' hj1 hj2 => ?_⟩, h⟩
        rcases hq.2.2 j'.succ (by simpa using hj1) (by simpa using hj2) with hlt | ⟨hweq, hle⟩ <;>
          [exact .inl hlt; exact .inr ⟨hweq, Nat.le_of_succ_le_succ hle⟩]

private theorem allPairs_pairwise_pairOrderLT (n : ℕ) :
    (allPairs n).Pairwise (fun p₁ p₂ =>
      p₁.1.val < p₁.2.val ∧ p₂.1.val < p₂.2.val ∧
        pairOrderLT (p₁.1.val, p₁.2.val) (p₂.1.val, p₂.2.val)) := by
  rw [allPairs, List.pairwise_flatMap]
  refine ⟨fun b _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact (List.pairwise_iff_getElem.mpr fun i j hi hj hij => by simpa using hij).imp
      fun {a₁ a₂} ha => ⟨a₁.isLt, a₂.isLt, .inr ⟨rfl, ha⟩⟩
  · refine (show (List.finRange n).Pairwise (fun b₁ b₂ : Fin n => b₁.val < b₂.val) from
      List.pairwise_iff_getElem.mpr fun _ _ _ _ hij => by simpa using hij).imp
        fun {b₁ b₂} hb_lt p₁ hp₁ p₂ hp₂ => ?_
    rw [List.mem_map] at hp₁ hp₂
    obtain ⟨a₁, _, rfl⟩ := hp₁; obtain ⟨a₂, _, rfl⟩ := hp₂
    exact ⟨a₁.isLt, a₂.isLt, .inl hb_lt⟩

private theorem eq_dedupSimpleEdges_of_pairMin {n : ℕ} {es : List (IndexedEdge n)}
    {idList : List (Fin es.length)}
    (hpw : idList.Pairwise fun q₁ q₂ =>
      pairOrderLT (edgePairNat es[q₁.val]) (edgePairNat es[q₂.val]))
    (hmin : ∀ q ∈ idList, IsPairMin es (edgePairNat es[q.val]) q)
    (hcov : ∀ i : Fin es.length, es[i.val].u ≠ es[i.val].v →
      ∃ q ∈ idList, edgePairNat es[q.val] = edgePairNat es[i.val]) :
    idList.map (fun q => es[q.val].toWeighted) =
      dedupSimpleEdges (es.map IndexedEdge.toWeighted) := by
  let L₁ := idList.map fun q => es[q.val].toWeighted
  let L₂ := dedupSimpleEdges (es.map IndexedEdge.toWeighted)
  have hL2_eq : L₂ = (allPairs n).filterMap fun p =>
      minFoldPair p (es.map IndexedEdge.toWeighted) := rfl
  let wLT : WeightedEdge n ℕ → WeightedEdge n ℕ → Prop :=
    fun ew₁ ew₂ => pairOrderLT (weightedPairNat ew₁) (weightedPairNat ew₂)
  have hpw₁ : L₁.Pairwise wLT := by rw [List.pairwise_map]; exact hpw.imp fun h => h
  have hpw₂ : L₂.Pairwise wLT := by
    rw [hL2_eq]
    refine (allPairs_pairwise_pairOrderLT n).filterMap _
      fun p₁ p₂ ⟨hp₁, hp₂, hlt⟩ ew₁ hew₁ ew₂ hew₂ => ?_
    obtain ⟨q₁, hq₁, rfl⟩ := (minFoldPair_eq_some_iff hp₁ es ew₁).mp hew₁
    obtain ⟨q₂, hq₂, rfl⟩ := (minFoldPair_eq_some_iff hp₂ es ew₂).mp hew₂
    change pairOrderLT (edgePairNat es[q₁.val]) (edgePairNat es[q₂.val])
    rw [hq₁.2.1, hq₂.2.1]; exact hlt
  have hnd₁ : L₁.Nodup :=
    (hpw₁.imp fun {x y} h (he : x = y) => pairOrderLT_irrefl _ (by rwa [he] at h)).nodup
  have hnd₂ : L₂.Nodup :=
    (hpw₂.imp fun {x y} h (he : x = y) => pairOrderLT_irrefl _ (by rwa [he] at h)).nodup
  have hmem : ∀ ew, ew ∈ L₁ ↔ ew ∈ L₂ := fun ew => ⟨fun h => by
      rw [List.mem_map] at h; obtain ⟨q, hq, rfl⟩ := h; have hmin_q := hmin q hq
      let a : Fin n := ⟨(edgePairNat es[q.val]).1, by
        dsimp only [edgePairNat]; split_ifs <;> exact Fin.isLt _⟩
      let b : Fin n := ⟨(edgePairNat es[q.val]).2, by
        dsimp only [edgePairNat]; split_ifs <;> exact Fin.isLt _⟩
      have hab : a.val < b.val := by
        have hne : es[q.val].u.val ≠ es[q.val].v.val := fun h' => hmin_q.1 (Fin.ext h')
        dsimp only [a, b, edgePairNat]; split_ifs <;> omega
      rw [hL2_eq, List.mem_filterMap]
      exact ⟨(a, b), mem_allPairs_iff.mpr hab,
        (minFoldPair_eq_some_iff hab es _).mpr ⟨q, hmin_q, rfl⟩⟩,
    fun h => by
      rw [hL2_eq, List.mem_filterMap] at h; obtain ⟨p, hp_all, hp_some⟩ := h
      obtain ⟨q, hq_min, rfl⟩ := (minFoldPair_eq_some_iff (allPairs_lt hp_all) es ew).mp hp_some
      obtain ⟨q', hq', heq⟩ := hcov q hq_min.1
      have hq'_min := hmin q' hq'; rw [heq, hq_min.2.1] at hq'_min
      rw [isPairMin_unique hq_min hq'_min]; exact List.mem_map.mpr ⟨q', hq', rfl⟩⟩
  exact ((List.perm_ext_iff_of_nodup hnd₁ hnd₂).mpr hmem).eq_of_pairwise
    (fun _ _ _ _ h₁ h₂ => absurd h₁ (fun h => pairOrderLT_asymm h h₂)) hpw₁ hpw₂

private theorem dedupSimpleEdges_nil_of_prepRows_empty {n : ℕ} {es : List (IndexedEdge n)}
    (hempty : (prepRows es es.length).length = 0) :
    ([] : List (IndexedEdge n)).map IndexedEdge.toWeighted =
      dedupSimpleEdges (es.map IndexedEdge.toWeighted) :=
  eq_dedupSimpleEdges_of_pairMin List.Pairwise.nil (fun _ h => by cases h) fun i hi => by
    have := List.length_pos_of_mem (mem_prepRows_of_ne i hi); omega

/-! ## Pass 1: Edge normalization and self-loop filtering (`dedupPrepStep`) -/

private structure DedupPrepEnv where
  edgeBase : ℕ
  normBase : ℕ

private word_enc_structure encDedupPrepEnv : DedupPrepEnv where
  edgeBase : wordWords,
  normBase : wordWords

private instance : WordEncoding DedupPrepEnv := ⟨2, encDedupPrepEnv⟩

private structure DedupPrepState where
  idx : ℕ
  outCount : ℕ

private word_enc_structure encDedupPrepState : DedupPrepState where
  idx : wordWords,
  outCount : wordWords

private instance : WordEncoding DedupPrepState := ⟨2, encDedupPrepState⟩

private def dedupPrepStep (x : DedupPrepEnv × DedupPrepState) : Memory.Prog DedupPrepState := do
  let env := x.1
  let st := x.2
  let u ← Memory.read (env.edgeBase + 4 * st.idx)
  let v ← Memory.read (env.edgeBase + 4 * st.idx + 1)
  if u = v then
    pure ⟨st.idx + 1, st.outCount⟩
  else if u < v then do
    Memory.write (env.normBase + 3 * st.outCount) u
    Memory.write (env.normBase + 3 * st.outCount + 1) v
    Memory.write (env.normBase + 3 * st.outCount + 2) st.idx
    pure ⟨st.idx + 1, st.outCount + 1⟩
  else do
    Memory.write (env.normBase + 3 * st.outCount) v
    Memory.write (env.normBase + 3 * st.outCount + 1) u
    Memory.write (env.normBase + 3 * st.outCount + 2) st.idx
    pure ⟨st.idx + 1, st.outCount + 1⟩

private def dedupPrepStepSafe (w : ℕ) (x : DedupPrepEnv × DedupPrepState)
    (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (x.2.idx + 1) ∧ Fits w (x.2.outCount + 1) ∧
    x.1.edgeBase + 4 * x.2.idx + 1 < s.frontier ∧
    x.1.normBase + 3 * x.2.outCount + 2 < s.frontier

private theorem realizes_dedupPrepStep : Realizes .exact
    dedupPrepStep (appendWords encDedupPrepEnv encDedupPrepState) encDedupPrepState
    dedupPrepStepSafe (fun _ _ => 0) := by
  unfold dedupPrepStep
  realize
  all_goals
    rcases h with ⟨h16, h1, h2, h3, h4⟩
    have hfront := hmem.frontier_fits
    fits

private theorem dedupPrep_write_ft {w normBase m idx a b : ℕ}
    {rows : List (Fin 3 → ℕ)} {t : Memory.State}
    (_hwt : Memory.WellFormed w t) (hk_lt : rows.length < m)
    (hnorm_lt : normBase + 3 * m ≤ t.frontier)
    (hfa : Fits w a) (hfb : Fits w b) (hfi : Fits w idx)
    (hrows : HoldsRecords 3 normBase rows t.mem) :
    let k := rows.length
    Memory.FramedTriple w t (do
      Memory.write (normBase + 3 * k) a
      Memory.write (normBase + 3 * k + 1) b
      Memory.write (normBase + 3 * k + 2) idx
      pure (⟨idx + 1, k + 1⟩ : DedupPrepState)) 3
      (Set.Ico normBase (normBase + 3 * m)) fun res t' =>
        res = ⟨idx + 1, k + 1⟩ ∧ t'.frontier = t.frontier ∧
        HoldsRecords 3 normBase (rows ++ [![a, b, idx]]) t'.mem := by
  let k := rows.length
  refine Memory.FramedTriple.write_bind_of_mem (by omega) hfa ⟨Nat.le_add_right _ _, by omega⟩ ?_
  refine Memory.FramedTriple.write_bind_of_mem (by dsimp only; omega) hfb ⟨by omega, by omega⟩ ?_
  refine Memory.FramedTriple.write_bind_of_mem (by dsimp only; omega) hfi ⟨by omega, by omega⟩ ?_
  refine Memory.FramedTriple.pure ⟨rfl, rfl, fun q hq j => ?_⟩
  rw [List.length_append, List.length_singleton] at hq
  by_cases hq_old : q < k
  · have hold := hrows q hq_old j; have hj_lt : j.val < 3 := j.isLt
    rw [List.getElem_append_left hq_old]; dsimp only [k] at hq_old ⊢
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]; exact hold
  · obtain rfl : q = rows.length := by dsimp only [k] at hq_old; omega
    rw [List.getElem_append_right (le_refl _), List.getElem_singleton]
    rcases j with ⟨_ | _ | _ | j, hj⟩ <;>
      first
      | exact absurd hj (by omega)
      | (simp only [Function.update_apply]; split_ifs <;> first | rfl | omega)

private theorem dedupPrep_framed {w n edgeBase normBase : ℕ} {es : List (IndexedEdge n)}
    {s : Memory.State} (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hin_lt : edgeBase + 4 * es.length ≤ s.frontier)
    (hnorm_lt : normBase + 3 * es.length ≤ s.frontier)
    (hdisj : edgeBase + 4 * es.length ≤ normBase)
    (hfit_m1 : Fits w (es.length + 1)) :
    let prog := iterate dedupPrepStep ⟨edgeBase, normBase⟩ es.length ⟨0, 0⟩
    iterationSafe dedupPrepStep dedupPrepStepSafe w ⟨edgeBase, normBase⟩ es.length ⟨0, 0⟩ s ∧
    Memory.FramedTriple w s prog (5 * es.length)
      (Set.Ico normBase (normBase + 3 * es.length)) fun res s' =>
        res = ⟨es.length, (prepRows es es.length).length⟩ ∧
        s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        HoldsRecords 3 normBase (prepRows es es.length) s'.mem := by
  let m := es.length; let S := Set.Ico normBase (normBase + 3 * m)
  let inv (i : ℕ) (st : DedupPrepState) (t : Memory.State) : Prop :=
    i ≤ m ∧ st = ⟨i, (prepRows es i).length⟩ ∧ t.frontier = s.frontier ∧
    Memory.WellFormed w t ∧ HoldsIndexedEdges edgeBase es t.mem ∧
    HoldsRecords 3 normBase (prepRows es i) t.mem
  have hstep : ∀ i < m, ∀ st t, inv i st t →
      let step := dedupPrepStep (⟨edgeBase, normBase⟩, st)
      dedupPrepStepSafe w (⟨edgeBase, normBase⟩, st) t ∧
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t step) ∧
      memoryCost step t + 0 ≤ 0 + 5 ∧
      Memory.Modifies S t ((Memory.spec 0).clientState t step) ∧
      inv (i + 1) ((Memory.spec 0).clientResult t step) ((Memory.spec 0).clientState t step) := by
    intro i hi st t ⟨hi_le, hst_eq, htfr, hwt, hin_t, hrows⟩; subst hst_eq
    have hplen := prepRows_length_le es i; obtain ⟨hu, hv, _, _⟩ := hin_t i hi
    have hfu : Fits w es[i].u.val := hu ▸ hwt.mem_fits _
    have hfv : Fits w es[i].v.val := hv ▸ hwt.mem_fits _
    have hfi : Fits w i := hfit_m1.of_le (by omega)
    have hsafe : dedupPrepStepSafe w (⟨edgeBase, normBase⟩, ⟨i, (prepRows es i).length⟩) t :=
      ⟨h16, hfit_m1.of_le (by dsimp only [m] at *; omega),
        hfit_m1.of_le (by dsimp only [m] at *; omega),
        by rw [htfr]; dsimp only [m] at *; omega, by rw [htfr]; dsimp only [m] at *; omega⟩
    have hft_step : Memory.FramedTriple w t
        (dedupPrepStep (⟨edgeBase, normBase⟩, ⟨i, (prepRows es i).length⟩)) 5 S fun res t' =>
          res = ⟨i + 1, (prepRows es (i + 1)).length⟩ ∧ t'.frontier = s.frontier ∧
          Memory.WellFormed w t' ∧ HoldsRecords 3 normBase (prepRows es (i + 1)) t'.mem := by
      have hsucc := prepRows_succ es hi; dsimp only [dedupPrepStep]
      refine Memory.FramedTriple.read_bind (c := 4) (by rw [htfr]; dsimp only [m] at *; omega) ?_
      rw [hu]
      refine (Memory.FramedTriple.read_bind (c := 3)
        (by rw [htfr]; dsimp only [m] at *; omega) ?_).mono (by omega) fun _ _ h => h
      rw [hv]
      by_cases huv : es[i].u.val = es[i].v.val
      · simp only [huv, ↓reduceIte]
        have hrows_eq : prepRows es (i + 1) = prepRows es i := by rw [hsucc]; simp [Fin.ext huv]
        exact Memory.FramedTriple.pure ⟨by rw [hrows_eq], htfr, hwt, by rw [hrows_eq]; exact hrows⟩
      · simp only [huv, ↓reduceIte]
        have hne_u : es[i].u ≠ es[i].v := fun h => huv (congrArg Fin.val h)
        have hlt_m : (prepRows es i).length < m := Nat.lt_of_le_of_lt hplen hi
        have hwrite_pair : ∀ a b, Fits w a → Fits w b →
            prepRows es (i + 1) = prepRows es i ++ [![a, b, i]] →
            Memory.FramedTriple w t (do
              Memory.write (normBase + 3 * (prepRows es i).length) a
              Memory.write (normBase + 3 * (prepRows es i).length + 1) b
              Memory.write (normBase + 3 * (prepRows es i).length + 2) i
              pure (⟨i + 1, (prepRows es i).length + 1⟩ : DedupPrepState)) 3 S fun res t' =>
                res = ⟨i + 1, (prepRows es (i + 1)).length⟩ ∧ t'.frontier = s.frontier ∧
                Memory.WellFormed w t' ∧ HoldsRecords 3 normBase (prepRows es (i + 1)) t'.mem :=
          fun a b hfa hfb hrows_eq =>
            ((dedupPrep_write_ft hwt hlt_m (by rw [htfr]; exact hnorm_lt)
              hfa hfb hfi hrows).wellFormed hwt).mono le_rfl
              fun res t' ⟨⟨hres, ht'fr, ht'rows⟩, ht'wf⟩ => by
                rw [hrows_eq]
                exact ⟨by simpa [hrows_eq] using hres, ht'fr.trans htfr, ht'wf, ht'rows⟩
        by_cases huv_lt : es[i].u.val < es[i].v.val <;>
        · simp only [huv_lt, ↓reduceIte]
          exact hwrite_pair _ _ (by first | exact hfu | exact hfv)
            (by first | exact hfv | exact hfu)
            (by rw [hsucc]; simp [hne_u, edgeRow, edgePairNat, huv_lt])
    obtain ⟨hv_step, _, hmod_step, hres_step, ht'fr, ht'wf, ht'rows⟩ :=
      framedTriple_iff_realization.mp hft_step
    exact ⟨hsafe, hv_step, by omega, hmod_step, by omega, hres_step, ht'fr, ht'wf,
      hin_t.congr (fun x _ hx => hmod_step.mem_eq_of_not_mem
        (by rw [htfr]; dsimp only [m] at *; omega) (by simp only [S, Set.mem_Ico]; omega)),
      ht'rows⟩
  obtain ⟨hsafe_it, hv_it, hm_it, hmod_it, _, hres_it, hfr_it, hwf_it, _, hrows_it⟩ :=
    iterate_potential_spec dedupPrepStep dedupPrepStepSafe w ⟨edgeBase, normBase⟩ 5 m inv
      (fun _ _ _ => 0) S hstep ⟨0, 0⟩ s
      ⟨Nat.zero_le m, rfl, rfl, hwf, hin, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  exact ⟨hsafe_it, framedTriple_iff_realization.mpr ⟨hv_it, by simpa using hm_it, hmod_it,
    hres_it, hfr_it, hwf_it, hrows_it⟩⟩

/-! ## Pass 2: Scanning pair-sorted triples (`dedupScanStep`, `dedupSortedProg`) -/

private structure DedupScanEnv where
  edgeBase : ℕ
  sortedBase : ℕ
  outBase : ℕ

private word_enc_structure encDedupScanEnv : DedupScanEnv where
  edgeBase : wordWords,
  sortedBase : wordWords,
  outBase : wordWords

private instance : WordEncoding DedupScanEnv := ⟨3, encDedupScanEnv⟩

private structure DedupScanState where
  idx : ℕ
  curA : ℕ
  curB : ℕ
  bestIdx : ℕ
  bestWeight : ℕ
  outCount : ℕ

private word_enc_structure encDedupScanState : DedupScanState where
  idx : wordWords,
  curA : wordWords,
  curB : wordWords,
  bestIdx : wordWords,
  bestWeight : wordWords,
  outCount : wordWords

private instance : WordEncoding DedupScanState := ⟨6, encDedupScanState⟩

private def dedupScanStep (x : DedupScanEnv × DedupScanState) : Memory.Prog DedupScanState := do
  let env := x.1
  let st := x.2
  let a ← Memory.read (env.sortedBase + 3 * st.idx)
  let b ← Memory.read (env.sortedBase + 3 * st.idx + 1)
  let idx ← Memory.read (env.sortedBase + 3 * st.idx + 2)
  let wEdge ← Memory.read (env.edgeBase + 4 * idx + 2)
  if a = st.curA then
    if b = st.curB then
      if wEdge < st.bestWeight then
        pure ⟨st.idx + 1, st.curA, st.curB, idx, wEdge, st.outCount⟩
      else
        pure ⟨st.idx + 1, st.curA, st.curB, st.bestIdx, st.bestWeight, st.outCount⟩
    else do
      copyIndexedEdge ⟨env.edgeBase, env.outBase, st.bestIdx, st.outCount⟩
      pure ⟨st.idx + 1, a, b, idx, wEdge, st.outCount + 1⟩
  else do
    copyIndexedEdge ⟨env.edgeBase, env.outBase, st.bestIdx, st.outCount⟩
    pure ⟨st.idx + 1, a, b, idx, wEdge, st.outCount + 1⟩

private def dedupScanStepSafe (w : ℕ) (x : DedupScanEnv × DedupScanState)
    (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (x.2.idx + 1) ∧ Fits w (x.2.outCount + 1) ∧
    x.1.sortedBase + 3 * x.2.idx + 2 < s.frontier ∧
    x.1.edgeBase + 4 * x.2.bestIdx + 4 ≤ s.frontier ∧
    x.1.outBase + 4 * x.2.outCount + 4 ≤ s.frontier ∧
    x.1.edgeBase + 4 * s.mem (x.1.sortedBase + 3 * x.2.idx + 2) + 2 < s.frontier

private theorem realizes_dedupScanStep : Realizes .exact
    dedupScanStep (appendWords encDedupScanEnv encDedupScanState) encDedupScanState
    dedupScanStepSafe (fun _ _ => 0) := by
  unfold dedupScanStep
  realize [realizes_copyIndexedEdge]
  all_goals
    rcases h with ⟨h16, h1, h2, h3, h4, h5, h6⟩
    have hfront := hmem.frontier_fits
    first | exact h16 | exact h4 | exact h5 | fits

private structure DedupSortedArgs where
  numVertices : ℕ
  edgeBase : ℕ
  sortedBase : ℕ
  count : ℕ

private word_enc_structure encDedupSortedArgs : DedupSortedArgs where
  numVertices : wordWords,
  edgeBase : wordWords,
  sortedBase : wordWords,
  count : wordWords

private instance : WordEncoding DedupSortedArgs := ⟨4, encDedupSortedArgs⟩

private def dedupSortedProg (a : DedupSortedArgs) : Memory.Prog GraphSlice := do
  let out ← Memory.allocBlockDirty (4 * a.count)
  let curA0 ← Memory.read a.sortedBase
  let curB0 ← Memory.read (a.sortedBase + 1)
  let bestIdx0 ← Memory.read (a.sortedBase + 2)
  let bestW0 ← Memory.read (a.edgeBase + 4 * bestIdx0 + 2)
  let stScan ← iterate dedupScanStep ⟨a.edgeBase, a.sortedBase, out.base⟩ (a.count - 1)
    ⟨1, curA0, curB0, bestIdx0, bestW0, 0⟩
  copyIndexedEdge ⟨a.edgeBase, out.base, stScan.bestIdx, stScan.outCount⟩
  pure ⟨a.numVertices, stScan.outCount + 1, out.base⟩

private def dedupSortedProgSafe (w : ℕ) (a : DedupSortedArgs) (s : Memory.State) : Prop :=
  let outBase := s.frontier
  let s₀ : Memory.State := ⟨s.mem, outBase + 4 * a.count⟩
  let st₀ : DedupScanState :=
    ⟨1, s.mem a.sortedBase, s.mem (a.sortedBase + 1), s.mem (a.sortedBase + 2),
      s.mem (a.edgeBase + 4 * s.mem (a.sortedBase + 2) + 2), 0⟩
  let it := iterate dedupScanStep ⟨a.edgeBase, a.sortedBase, outBase⟩ (a.count - 1) st₀
  let stEnd := (Memory.spec 0).clientResult s₀ it
  let s₁ := (Memory.spec 0).clientState s₀ it
  Fits w 16 ∧ Fits w (a.count + 1) ∧ Fits w (4 * a.count) ∧ Fits w (outBase + 4 * a.count) ∧
    a.sortedBase + 2 < outBase + 4 * a.count ∧
    a.edgeBase + 4 * s.mem (a.sortedBase + 2) + 2 < outBase + 4 * a.count ∧
    Fits w (stEnd.outCount + 1) ∧
    a.edgeBase + 4 * stEnd.bestIdx + 4 ≤ s₁.frontier ∧
    outBase + 4 * stEnd.outCount + 4 ≤ s₁.frontier ∧
    iterationSafe dedupScanStep dedupScanStepSafe w ⟨a.edgeBase, a.sortedBase, outBase⟩
      (a.count - 1) st₀ s₀ ∧
    1 ≤ a.count

private theorem realizes_dedupSortedProg : Realizes .exact
    dedupSortedProg encDedupSortedArgs encGraphSlice dedupSortedProgSafe (fun _ _ => 0) := by
  unfold dedupSortedProg
  realize [realizes_dedupScanStep, realizes_copyIndexedEdge]
  all_goals
    rcases h with ⟨h16, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    repeat rw [Memory.clientState_allocBlockDirty] at *
    try simp only [Memory.clientResult_allocBlockDirty] at h9 h7 h8 ⊢
    have hfront := hmem.frontier_fits
    first
    | exact h10 | exact iterationSafe_imp h9 (fun _ => rfl) (fun _ _ hs => hs)
    | exact h16 | exact h7 | exact h8 | fits [h1, h2, h3, h6]

private theorem holdsIndexedEdges_append_single {n outBase : ℕ} {es : List (IndexedEdge n)}
    {idPref : List (Fin es.length)} {bestIdx : Fin es.length} {mem : ℕ → ℕ}
    (hpref : HoldsIndexedEdges outBase (idPref.map fun q => es[q.val]) mem)
    (hu : mem (outBase + 4 * idPref.length) = es[bestIdx.val].u.val)
    (hv : mem (outBase + 4 * idPref.length + 1) = es[bestIdx.val].v.val)
    (hw : mem (outBase + 4 * idPref.length + 2) = es[bestIdx.val].weight)
    (hid : mem (outBase + 4 * idPref.length + 3) = es[bestIdx.val].id) :
    HoldsIndexedEdges outBase ((idPref ++ [bestIdx]).map fun q => es[q.val]) mem := by
  intro p hp; simp only [List.length_map, List.length_append, List.length_singleton] at hp
  simp only [List.getElem_map]
  by_cases hp_old : p < idPref.length
  · have hm := hpref p (by simp [hp_old]); simp only [List.getElem_map] at hm
    rw [List.getElem_append_left hp_old]; exact hm
  · obtain rfl : p = idPref.length := by omega
    rw [List.getElem_append_right (le_refl _), List.getElem_singleton]; exact ⟨hu, hv, hw, hid⟩

private theorem copy_append_pref_framed {w n edgeBase outBase rowsLen : ℕ}
    {es : List (IndexedEdge n)} {idPref : List (Fin es.length)} {bestIdx : Fin es.length}
    {t : Memory.State} (hwf : Memory.WellFormed w t)
    (hpref : HoldsIndexedEdges outBase (idPref.map fun q => es[q.val]) t.mem)
    (hin : HoldsIndexedEdges edgeBase es t.mem)
    (hed_lt : edgeBase + 4 * es.length ≤ outBase) (hout_lt : outBase + 4 * rowsLen ≤ t.frontier)
    (hlen : idPref.length < rowsLen) :
    Memory.FramedTriple w t (copyIndexedEdge ⟨edgeBase, outBase, bestIdx.val, idPref.length⟩) 8
      (Set.Ico outBase (outBase + 4 * rowsLen)) fun _ t' =>
        t'.frontier = t.frontier ∧ Memory.WellFormed w t' ∧
        HoldsIndexedEdges outBase ((idPref ++ [bestIdx]).map fun q => es[q.val]) t'.mem := by
  have hb_lt := bestIdx.isLt
  have hcp := (holdsIndexedEdges_frame_mem
    (copyIndexedEdge_spec hwf (srcBase := edgeBase) (dstBase := outBase)
      (srcIdx := bestIdx.val) (dstIdx := idPref.length) (by omega) (by omega) (Or.inl (by omega)))
    hpref (Set.disjoint_left.mpr fun a ha hb => by
      simp only [Set.mem_Ico, List.length_map] at ha hb; omega)
    (by simp only [List.length_map]; omega)).frame_mono
    (S' := Set.Ico outBase (outBase + 4 * rowsLen))
    (fun x hx => by simp only [Set.mem_Ico] at hx ⊢; omega)
  obtain ⟨hbu, hbv, hbw, hbid⟩ := hin bestIdx.val hb_lt
  exact hcp.mono le_rfl fun _ t' ⟨⟨ht'fr, ht'wf, ht'copy⟩, ht'pref⟩ =>
    ⟨ht'fr, ht'wf, holdsIndexedEdges_append_single ht'pref
      ((ht'copy 0 (by decide)).trans hbu) ((ht'copy 1 (by decide)).trans hbv)
      ((ht'copy 2 (by decide)).trans hbw) ((ht'copy 3 (by decide)).trans hbid)⟩

private abbrev rowPair (r : Fin 3 → ℕ) : ℕ × ℕ := (r 0, r 1)

private theorem pairIdxLT_pair_lt_of_step {rows : List (Fin 3 → ℕ)} {r : ℕ}
    (hsorted : rows.Pairwise pairIdxLT) (hr1 : r + 1 < rows.length)
    (hne : rowPair (rows[r + 1]'hr1) ≠ rowPair (rows[r]'(Nat.lt_of_succ_lt hr1))) :
    pairOrderLT (rowPair (rows[r]'(Nat.lt_of_succ_lt hr1))) (rowPair (rows[r + 1]'hr1)) ∧
    ∀ j, r < j → (hjl : j < rows.length) →
      pairOrderLT (rowPair (rows[r]'(Nat.lt_of_succ_lt hr1))) (rowPair (rows[j]'hjl)) := by
  have hr_lt := Nat.lt_of_succ_lt hr1
  have hlex : pairOrderLT (rowPair (rows[r]'hr_lt)) (rowPair (rows[r + 1]'hr1)) := by
    rcases List.pairwise_iff_getElem.mp hsorted r (r + 1) hr_lt hr1 (Nat.lt_succ_self r) with
      hlt | ⟨heq, _⟩ <;> [exact hlt; exact absurd heq.symm hne]
  refine ⟨hlex, fun j hj hjl => ?_⟩
  by_cases hj1 : j = r + 1
  · subst hj1; exact hlex
  · rcases List.pairwise_iff_getElem.mp hsorted (r + 1) j hr1 hjl (by omega) with hlt1 | ⟨heq1, _⟩
    · exact pairOrderLT_trans hlex hlt1
    · dsimp only [rowPair]; rw [← heq1]; exact hlex

private theorem idList_step_aux {n : ℕ} {es : List (IndexedEdge n)}
    {idPref : List (Fin es.length)} {bestIdx : Fin es.length} {p : ℕ × ℕ}
    (hpw : idPref.Pairwise fun q₁ q₂ => pairOrderLT (edgePairNat es[q₁.val])
      (edgePairNat es[q₂.val]))
    (hall : ∀ q ∈ idPref, pairOrderLT (edgePairNat es[q.val]) p)
    (hpref_min : ∀ q ∈ idPref, IsPairMin es (edgePairNat es[q.val]) q)
    (hbi_cp : edgePairNat es[bestIdx.val] = p)
    (hbi_min : IsPairMin es (edgePairNat es[bestIdx.val]) bestIdx) :
    (idPref ++ [bestIdx]).Pairwise (fun q₁ q₂ =>
      pairOrderLT (edgePairNat es[q₁.val]) (edgePairNat es[q₂.val])) ∧
    (∀ q ∈ idPref ++ [bestIdx], IsPairMin es (edgePairNat es[q.val]) q) := by
  refine ⟨List.pairwise_append.mpr ⟨hpw, List.pairwise_singleton _ _, fun q hq _ hb => ?_⟩,
    fun q hq => ?_⟩
  · simp only [List.mem_singleton] at hb; subst hb; rw [hbi_cp]; exact hall q hq
  · rw [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq_old | rfl <;> [exact hpref_min q hq_old; exact hbi_min]

private theorem isPairMin_of_prefix {n r : ℕ} {es : List (IndexedEdge n)} {rows : List (Fin 3 → ℕ)}
    (hr_lt : r < rows.length) (hperm : rows.Perm (prepRows es es.length)) (bestIdx : Fin es.length)
    (hbest_ne : es[bestIdx.val].u ≠ es[bestIdx.val].v)
    (hbest_pair : edgePairNat es[bestIdx.val] = rowPair (rows[r]'hr_lt))
    (hprefix_min : ∀ idx (hidx : idx ≤ r) (q : Fin es.length),
      (rows[idx]'(Nat.lt_of_le_of_lt hidx hr_lt)) 2 = q.val →
      rowPair (rows[idx]'(Nat.lt_of_le_of_lt hidx hr_lt)) = rowPair (rows[r]'hr_lt) →
        es[bestIdx.val].weight < es[q.val].weight ∨
        (es[bestIdx.val].weight = es[q.val].weight ∧ bestIdx.val ≤ q.val))
    (hlast : ∀ j (_hj : r < j) (hjl : j < rows.length),
      rowPair (rows[j]'hjl) ≠ rowPair (rows[r]'hr_lt)) :
    IsPairMin es (edgePairNat es[bestIdx.val]) bestIdx := by
  refine ⟨hbest_ne, rfl, fun i hi_ne hi_cp => ?_⟩
  have hmem_row : edgeRow es[i.val] i.val ∈ rows := hperm.symm.subset (mem_prepRows_of_ne i hi_ne)
  rw [List.mem_iff_getElem] at hmem_row; obtain ⟨idx, hidx_lt, hidx_eq⟩ := hmem_row
  have hpair_idx : rowPair (rows[idx]'hidx_lt) = rowPair (rows[r]'hr_lt) := by
    rw [← hbest_pair, ← hi_cp, hidx_eq]; rfl
  have hidx_le : idx ≤ r := by
    by_contra hgt; exact hlast idx (Nat.lt_of_not_le hgt) hidx_lt hpair_idx
  exact hprefix_min idx hidx_le i (by rw [hidx_eq]; rfl) hpair_idx

private def dedupScanInv {n : ℕ} (outBase : ℕ) (es : List (IndexedEdge n))
    (rows : List (Fin 3 → ℕ)) (r : ℕ) (hr : r < rows.length)
    (st : DedupScanState) (mem : ℕ → ℕ) : Prop :=
  ∃ (idPref : List (Fin es.length)) (bestIdx : Fin es.length) (bestPos : ℕ),
    ∃ hbp : bestPos ≤ r, (rows[bestPos]'(Nat.lt_of_le_of_lt hbp hr)) 2 = bestIdx.val ∧
      st = ⟨r + 1, (rows[r]'hr) 0, (rows[r]'hr) 1, bestIdx.val,
        es[bestIdx.val].weight, idPref.length⟩ ∧
      idPref.length ≤ r ∧ edgePairNat es[bestIdx.val] = rowPair (rows[r]'hr) ∧
      HoldsIndexedEdges outBase (idPref.map fun q => es[q.val]) mem ∧
      idPref.Pairwise (fun q₁ q₂ => pairOrderLT (edgePairNat es[q₁.val])
        (edgePairNat es[q₂.val])) ∧
      (∀ q ∈ idPref, pairOrderLT (edgePairNat es[q.val]) (rowPair (rows[r]'hr))) ∧
      (∀ q ∈ idPref, IsPairMin es (edgePairNat es[q.val]) q) ∧
      (∀ idx (hidx : idx ≤ r) (q : Fin es.length),
        (rows[idx]'(Nat.lt_of_le_of_lt hidx hr)) 2 = q.val →
        rowPair (rows[idx]'(Nat.lt_of_le_of_lt hidx hr)) = rowPair (rows[r]'hr) →
          es[bestIdx.val].weight < es[q.val].weight ∨
          (es[bestIdx.val].weight = es[q.val].weight ∧ bestIdx.val ≤ q.val)) ∧
      (∀ idx (hidx : idx ≤ r),
        rowPair (rows[idx]'(Nat.lt_of_le_of_lt hidx hr)) ≠ rowPair (rows[r]'hr) →
          ∃ q ∈ idPref, edgePairNat es[q.val] = rowPair (rows[idx]'(Nat.lt_of_le_of_lt hidx hr)))

private theorem dedupScanStep_framed {w n edgeBase sortedBase outBase s0Front r : ℕ}
    {es : List (IndexedEdge n)} {rows : List (Fin 3 → ℕ)} {st : DedupScanState}
    {t : Memory.State}
    (h16 : Fits w 16) (hwt : Memory.WellFormed w t) (htfr : t.frontier = s0Front)
    (hrows_t : HoldsRecords 3 sortedBase rows t.mem)
    (hin_t : HoldsIndexedEdges edgeBase es t.mem)
    (hed_lt : edgeBase + 4 * es.length ≤ outBase)
    (hxs_lt : sortedBase + 3 * rows.length ≤ outBase)
    (hout_lt : outBase + 4 * rows.length ≤ s0Front)
    (hfit_k1 : Fits w (rows.length + 1))
    (hperm : rows.Perm (prepRows es es.length))
    (hsorted : rows.Pairwise pairIdxLT)
    (hcorr : ∀ x ∈ rows, ∃ hlt : x 2 < es.length, es[x 2].u ≠ es[x 2].v ∧
      edgePairNat es[x 2] = (x 0, x 1) ∧ x 0 < x 1)
    (hr1_lt : r + 1 < rows.length)
    (hinv : dedupScanInv outBase es rows r (Nat.lt_of_succ_lt hr1_lt) st t.mem) :
    let S := Set.Ico outBase (outBase + 4 * rows.length)
    dedupScanStepSafe w (⟨edgeBase, sortedBase, outBase⟩, st) t ∧
    Memory.FramedTriple w t (dedupScanStep (⟨edgeBase, sortedBase, outBase⟩, st)) 12 S
      fun st' t' =>
        Memory.WellFormed w t' ∧ t'.frontier = s0Front ∧
        dedupScanInv outBase es rows (r + 1) hr1_lt st' t'.mem := by
  have hr_lt : r < rows.length := Nat.lt_of_succ_lt hr1_lt
  let S := Set.Ico outBase (outBase + 4 * rows.length)
  obtain ⟨idPref, bestIdx, bestPos, hbp_le, hbp_idx, hst_eq, hlen_le, hbi_cp, hpref_mem, hpw_lt,
    hall_lt, hpref_min, hcur_min, hprev_cov⟩ := hinv
  subst hst_eq
  have hbp_lt : bestPos < rows.length := Nat.lt_of_le_of_lt hbp_le hr_lt
  let bestRow := rows[bestPos]'hbp_lt
  have hbp_corr := hcorr bestRow (List.getElem_mem hbp_lt)
  have hbp_ne : es[bestIdx.val].u ≠ es[bestIdx.val].v := by
    have h := hbp_corr.2.1; simpa only [bestRow, hbp_idx] using h
  let nextRow := rows[r + 1]'hr1_lt
  obtain ⟨hx_lt, _, hx_cp, _⟩ := hcorr nextRow (List.getElem_mem hr1_lt)
  let nextIdx : Fin es.length := ⟨nextRow 2, hx_lt⟩
  have ha := hrows_t (r + 1) hr1_lt 0
  have hb := hrows_t (r + 1) hr1_lt 1
  have hi := hrows_t (r + 1) hr1_lt 2
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.add_zero] at ha hb hi
  obtain ⟨_, _, hw_next, _⟩ := hin_t nextIdx.val hx_lt
  dsimp only [dedupScanStepSafe, dedupScanStep]
  refine ⟨⟨h16, hfit_k1.of_le (by omega), hfit_k1.of_le (by omega), by rw [htfr]; omega,
    by have := bestIdx.isLt; rw [htfr]; omega, by rw [htfr]; omega,
    by rw [htfr, hi]; have : (rows[r + 1]'hr1_lt) 2 < es.length := hx_lt; omega⟩, ?_⟩
  refine Memory.FramedTriple.read_bind (by rw [htfr]; omega) ?_; rw [ha]
  refine Memory.FramedTriple.read_bind (by rw [htfr]; omega) ?_; rw [hb]
  refine Memory.FramedTriple.read_bind (by rw [htfr]; omega) ?_; rw [hi]
  refine Memory.FramedTriple.read_bind
    (by rw [htfr]; have : (rows[r + 1]'hr1_lt) 2 < es.length := hx_lt; omega) ?_
  rw [show (rows[r + 1]'hr1_lt) 2 = nextIdx.val from rfl, hw_next]
  by_cases heq_pair : rowPair nextRow = rowPair (rows[r]'hr_lt)
  · have hnr0 : (rows[r + 1]'hr1_lt) 0 = (rows[r]'hr_lt) 0 := congrArg Prod.fst heq_pair
    have hnr1 : (rows[r + 1]'hr1_lt) 1 = (rows[r]'hr_lt) 1 := congrArg Prod.snd heq_pair
    simp only [hnr0, hnr1, ↓reduceIte]
    have hidx_lt : bestIdx.val < nextIdx.val := by
      have hbp_pair : rowPair bestRow = rowPair nextRow := by
        have h1 : rowPair bestRow = edgePairNat es[bestIdx.val] := by
          have h := hbp_corr.2.2.1.symm; simpa only [bestRow, hbp_idx] using h
        exact h1.trans (hbi_cp.trans heq_pair.symm)
      rcases List.pairwise_iff_getElem.mp hsorted bestPos (r + 1) hbp_lt hr1_lt
          (Nat.lt_succ_of_le hbp_le) with hlt | ⟨_, h2lt⟩
      · dsimp only [rowPair, bestRow, nextRow] at hbp_pair
        exact absurd (hbp_pair ▸ hlt) (pairOrderLT_irrefl _)
      · simpa only [bestRow, hbp_idx] using h2lt
    have hsame_inv : ∀ (newBest : Fin es.length) (newPos : ℕ) (hle : newPos ≤ r + 1),
        (rows[newPos]'(Nat.lt_of_le_of_lt hle hr1_lt)) 2 = newBest.val →
        edgePairNat es[newBest.val] = rowPair (rows[r]'hr_lt) →
        (∀ idx (hidx : idx ≤ r) (q : Fin es.length),
          (rows[idx]'(Nat.lt_of_le_of_lt hidx hr_lt)) 2 = q.val →
          rowPair (rows[idx]'(Nat.lt_of_le_of_lt hidx hr_lt)) = rowPair (rows[r]'hr_lt) →
          es[newBest.val].weight < es[q.val].weight ∨
            (es[newBest.val].weight = es[q.val].weight ∧ newBest.val ≤ q.val)) →
        (es[newBest.val].weight < es[nextIdx.val].weight ∨
          (es[newBest.val].weight = es[nextIdx.val].weight ∧ newBest.val ≤ nextIdx.val)) →
        Memory.FramedTriple w t (pure ⟨r + 2, (rows[r]'hr_lt) 0, (rows[r]'hr_lt) 1,
          newBest.val, es[newBest.val].weight, idPref.length⟩) 8 S fun st' t' =>
            Memory.WellFormed w t' ∧ t'.frontier = s0Front ∧
            dedupScanInv outBase es rows (r + 1) hr1_lt st' t'.mem := fun
        newBest newPos hle hnp hcp hpref_c hlast_c =>
      (Memory.FramedTriple.pure (S := S)
        ⟨hwt, htfr, idPref, newBest, newPos, hle, hnp, by rw [hnr0, hnr1], by omega,
          hcp.trans heq_pair.symm, hpref_mem, hpw_lt, fun q hq => heq_pair ▸ hall_lt q hq,
          hpref_min, fun idx hidx q hq_val hpid => by
            by_cases hqr : idx ≤ r
            · exact hpref_c idx hqr q hq_val (hpid.trans heq_pair)
            · obtain rfl : idx = r + 1 := by omega
              obtain rfl : nextIdx = q := Fin.ext hq_val; exact hlast_c,
          fun idx hidx hpne =>
            hprev_cov idx (Nat.lt_succ_iff.mp
              (Nat.lt_of_le_of_ne hidx fun h => hpne (by subst h; rfl)))
              fun h => hpne (h.trans heq_pair.symm)⟩).mono (Nat.zero_le 8) fun _ _ h => h
    by_cases hw_lt : es[nextIdx.val].weight < es[bestIdx.val].weight
    · simp only [hw_lt, ↓reduceIte]
      exact hsame_inv nextIdx (r + 1) le_rfl rfl (hx_cp.trans heq_pair) (fun idx hqr q hqv hpid =>
        by rcases hcur_min idx hqr q hqv hpid with hlt | ⟨heq, _⟩ <;>
          [exact .inl (Nat.lt_trans hw_lt hlt); exact .inl (heq ▸ hw_lt)]) (.inr ⟨rfl, le_rfl⟩)
    · simp only [hw_lt, ↓reduceIte]
      exact hsame_inv bestIdx bestPos (Nat.le_succ_of_le hbp_le) hbp_idx hbi_cp hcur_min (by
        rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hw_lt) with heqw | hltw <;>
          [exact .inr ⟨heqw, Nat.le_of_lt hidx_lt⟩; exact .inl hltw])
  · obtain ⟨hlex, hlt_after⟩ := pairIdxLT_pair_lt_of_step hsorted hr1_lt heq_pair
    have hbi_min := isPairMin_of_prefix hr_lt hperm bestIdx hbp_ne hbi_cp hcur_min
      fun j hj hjl heqj => pairOrderLT_irrefl _ (heqj ▸ hlt_after j hj hjl)
    have hcp_copy := copy_append_pref_framed (bestIdx := bestIdx) hwt hpref_mem hin_t hed_lt
      (by rw [htfr]; omega) (Nat.lt_of_le_of_lt hlen_le hr_lt)
    obtain ⟨hpw_new, hmin_new⟩ := idList_step_aux hpw_lt hall_lt hpref_min hbi_cp hbi_min
    have hbranch : Memory.FramedTriple w t (do
          copyIndexedEdge ⟨edgeBase, outBase, bestIdx.val, idPref.length⟩
          pure ⟨r + 2, nextRow 0, nextRow 1, nextIdx.val, es[nextIdx.val].weight,
            idPref.length + 1⟩) 8 S fun st' t' =>
          Memory.WellFormed w t' ∧ t'.frontier = s0Front ∧
          dedupScanInv outBase es rows (r + 1) hr1_lt st' t'.mem := by
      refine Memory.FramedTriple.bind_same (c₁ := 8) (c₂ := 0) ?_
      refine hcp_copy.mono le_rfl fun _ t' ⟨ht'fr, ht'wf, ht'pref⟩ => ?_
      refine Memory.FramedTriple.pure ⟨ht'wf, ht'fr.trans htfr, idPref ++ [bestIdx],
        nextIdx, r + 1, le_rfl, rfl, by simp only [List.length_append, List.length_singleton]; rfl,
        by simp; omega, hx_cp, ht'pref,
        hpw_new, fun q hq => ?_, hmin_new, fun idx hidx q hq_val hpid => ?_,
        fun idx hidx hpne => ?_⟩
      · rw [List.mem_append, List.mem_singleton] at hq
        rcases hq with hq_old | rfl <;>
          [exact pairOrderLT_trans (hall_lt q hq_old) hlex; exact hbi_cp ▸ hlex]
      · by_cases hqr : idx ≤ r
        · exfalso
          by_cases hidx_eq : idx = r
          · subst hidx_eq; exact heq_pair hpid.symm
          · dsimp only [rowPair] at hpid heq_pair hlex
            rcases List.pairwise_iff_getElem.mp hsorted idx r
                (Nat.lt_of_le_of_lt hqr hr_lt) hr_lt (by omega) with hlt_ir | ⟨heq_ir, _⟩ <;>
              [exact pairOrderLT_asymm (hpid ▸ hlt_ir) hlex; exact heq_pair (heq_ir ▸ hpid).symm]
        · obtain rfl : idx = r + 1 := by omega
          obtain rfl : nextIdx = q := Fin.ext hq_val; exact .inr ⟨rfl, le_rfl⟩
      · by_cases hqr : idx ≤ r
        · by_cases hid_r : rowPair (rows[idx]'(Nat.lt_of_le_of_lt hqr hr_lt)) =
              rowPair (rows[r]'hr_lt)
          · exact ⟨bestIdx, List.mem_append_right _ (List.mem_singleton_self _),
              hbi_cp.trans hid_r.symm⟩
          · obtain ⟨q, hq, hqeq⟩ := hprev_cov idx hqr hid_r
            exact ⟨q, List.mem_append_left _ hq, hqeq⟩
        · obtain rfl : idx = r + 1 := (by omega); exact absurd rfl hpne
    by_cases h1 : (rows[r + 1]'hr1_lt) 0 = (rows[r]'hr_lt) 0
    · by_cases h2 : (rows[r + 1]'hr1_lt) 1 = (rows[r]'hr_lt) 1
      · exact absurd (Prod.ext h1 h2) heq_pair
      · rw [ite_eq_left h1, ite_eq_right h2]; exact hbranch
    · rw [ite_eq_right h1]; exact hbranch

private theorem dedupScan_framed {w n edgeBase sortedBase outBase : ℕ} {es : List (IndexedEdge n)}
    {rows : List (Fin 3 → ℕ)} {s₀ : Memory.State}
    (h16 : Fits w 16) (hwf₀ : Memory.WellFormed w s₀)
    (hrows : HoldsRecords 3 sortedBase rows s₀.mem)
    (hin : HoldsIndexedEdges edgeBase es s₀.mem) (hk_pos : 0 < rows.length)
    (hed_lt : edgeBase + 4 * es.length ≤ outBase) (hxs_lt : sortedBase + 3 * rows.length ≤ outBase)
    (hout_lt : outBase + 4 * rows.length ≤ s₀.frontier) (hfit_k1 : Fits w (rows.length + 1))
    (hperm : rows.Perm (prepRows es es.length)) (hsorted : rows.Pairwise pairIdxLT)
    (hcorr : ∀ x ∈ rows, ∃ hlt : x 2 < es.length, es[x 2].u ≠ es[x 2].v ∧
      edgePairNat es[x 2] = (x 0, x 1) ∧ x 0 < x 1) :
    let st₀ : DedupScanState := ⟨1, rows[0] 0, rows[0] 1, rows[0] 2,
      (es[rows[0] 2]'(hcorr rows[0] (List.getElem_mem hk_pos)).1).weight, 0⟩
    let prog := iterate dedupScanStep ⟨edgeBase, sortedBase, outBase⟩ (rows.length - 1) st₀
    let S := Set.Ico outBase (outBase + 4 * rows.length)
    iterationSafe dedupScanStep dedupScanStepSafe w ⟨edgeBase, sortedBase, outBase⟩
      (rows.length - 1) st₀ s₀ ∧
    Memory.FramedTriple w s₀ prog (12 * (rows.length - 1)) S fun st' s' =>
      s'.frontier = s₀.frontier ∧ Memory.WellFormed w s' ∧ HoldsIndexedEdges edgeBase es s'.mem ∧
      ∃ (idPref : List (Fin es.length)) (bestIdx : Fin es.length),
        st' = ⟨rows.length, (rows[rows.length - 1]'(Nat.sub_lt hk_pos Nat.one_pos)) 0,
          (rows[rows.length - 1]'(Nat.sub_lt hk_pos Nat.one_pos)) 1,
          bestIdx.val, es[bestIdx.val].weight, idPref.length⟩ ∧
        idPref.length ≤ rows.length - 1 ∧
        HoldsIndexedEdges outBase (idPref.map fun q => es[q.val]) s'.mem ∧
        idPref.Pairwise (fun q₁ q₂ => pairOrderLT (edgePairNat es[q₁.val])
          (edgePairNat es[q₂.val])) ∧
        (∀ q ∈ idPref, pairOrderLT (edgePairNat es[q.val])
          (rowPair (rows[rows.length - 1]'(Nat.sub_lt hk_pos Nat.one_pos)))) ∧
        (∀ q ∈ idPref, IsPairMin es (edgePairNat es[q.val]) q) ∧
        IsPairMin es (edgePairNat es[bestIdx.val]) bestIdx ∧
        edgePairNat es[bestIdx.val] =
          rowPair (rows[rows.length - 1]'(Nat.sub_lt hk_pos Nat.one_pos)) ∧
        ∀ i : Fin es.length, es[i.val].u ≠ es[i.val].v →
          ∃ q ∈ idPref ++ [bestIdx], edgePairNat es[q.val] = edgePairNat es[i.val] := by
  let k := rows.length; let S := Set.Ico outBase (outBase + 4 * k)
  let h0 := (hcorr rows[0] (List.getElem_mem hk_pos)).1
  let st₀ : DedupScanState := ⟨1, rows[0] 0, rows[0] 1, rows[0] 2, es[rows[0] 2].weight, 0⟩
  let inv (r : ℕ) (st : DedupScanState) (t : Memory.State) : Prop :=
    ∃ hr : r < k, t.frontier = s₀.frontier ∧ Memory.WellFormed w t ∧
    HoldsIndexedEdges edgeBase es t.mem ∧ HoldsRecords 3 sortedBase rows t.mem ∧
    dedupScanInv outBase es rows r hr st t.mem
  have hstep : ∀ r < k - 1, ∀ st t, inv r st t →
      let step := dedupScanStep (⟨edgeBase, sortedBase, outBase⟩, st)
      dedupScanStepSafe w (⟨edgeBase, sortedBase, outBase⟩, st) t ∧
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t step) ∧
      memoryCost step t + 0 ≤ 0 + 12 ∧
      Memory.Modifies S t ((Memory.spec 0).clientState t step) ∧
      inv (r + 1) ((Memory.spec 0).clientResult t step) ((Memory.spec 0).clientState t step) := by
    intro r hr st t ⟨hr_lt, htfr, hwt, hin_t, hrows_t, hinv_r⟩ step
    have hr1_lt : r + 1 < k := by omega
    obtain ⟨hsafe, hft_step⟩ := dedupScanStep_framed h16 hwt htfr hrows_t hin_t hed_lt hxs_lt
      hout_lt hfit_k1 hperm hsorted hcorr hr1_lt hinv_r
    obtain ⟨hv_step, _, hmod_step, hwt', ht'fr, hinv'⟩ := framedTriple_iff_realization.mp hft_step
    have hnot : ∀ a < s₀.frontier, a ∉ S →
        ((Memory.spec 0).clientState t step).mem a = t.mem a :=
      fun _ ha_lt ha => hmod_step.mem_eq_of_not_mem (by rw [htfr]; exact ha_lt) ha
    exact ⟨hsafe, hv_step, by omega, hmod_step, hr1_lt, ht'fr, hwt',
      hin_t.congr (fun x _ hx => hnot x (by omega) (by simp only [S, Set.mem_Ico]; omega)),
      hrows_t.congr (fun x _ hx => hnot x (by omega) (by simp only [S, Set.mem_Ico]; omega)), hinv'⟩
  have hinv0 : inv 0 st₀ s₀ :=
    ⟨hk_pos, rfl, hwf₀, hin, hrows, [], ⟨rows[0] 2, h0⟩, 0, le_rfl, rfl, rfl, Nat.zero_le 0,
      (hcorr rows[0] (List.getElem_mem hk_pos)).2.2.1, fun _ h => by simp at h,
      List.Pairwise.nil, fun _ h => by simp at h, fun _ h => by simp at h,
      (fun idx _ q hq_val _ => by
        obtain rfl : idx = 0 := by omega
        obtain rfl : (⟨rows[0] 2, h0⟩ : Fin _) = q := Fin.ext hq_val; exact .inr ⟨rfl, le_rfl⟩),
      fun idx _ hpne => by obtain rfl : idx = 0 := (by omega); exact absurd rfl hpne⟩
  obtain ⟨hsafe_it, hv_it, hm_it, hmod_it, _, htfr_end, hwf_end, hin_end, _, idPref, bestIdx,
      bestPos, hbp_end, hbp_idx_end, hst_end, hlen_end, hbi_cp, hpref_mem, hpw_lt, hall_lt,
      hpref_min, hcur_min, hprev_cov⟩ :=
    iterate_potential_spec dedupScanStep dedupScanStepSafe w ⟨edgeBase, sortedBase, outBase⟩ 12
      (k - 1) inv (fun _ _ _ => 0) S hstep st₀ s₀ hinv0
  have hk1_lt : k - 1 < k := Nat.sub_lt hk_pos Nat.one_pos
  have hbp_lt : bestPos < k := Nat.lt_of_le_of_lt hbp_end hk1_lt
  have hbp_ne : es[bestIdx.val].u ≠ es[bestIdx.val].v := by
    have h := (hcorr (rows[bestPos]'hbp_lt) (List.getElem_mem hbp_lt)).2.1
    simpa only [hbp_idx_end] using h
  have hbi_min := isPairMin_of_prefix hk1_lt hperm bestIdx hbp_ne hbi_cp hcur_min
    fun j hj _ => absurd hj (by omega)
  refine ⟨hsafe_it, framedTriple_iff_realization.mpr ⟨hv_it, by simpa using hm_it, hmod_it,
    htfr_end, hwf_end, hin_end, idPref, bestIdx,
    by simpa [k, Nat.sub_add_cancel hk_pos] using hst_end,
    by simpa [k] using hlen_end, hpref_mem, hpw_lt, hall_lt, hpref_min, hbi_min, hbi_cp, ?_⟩⟩
  intro i hi_ne
  have hmem_row : edgeRow es[i.val] i.val ∈ rows := hperm.symm.subset (mem_prepRows_of_ne i hi_ne)
  rw [List.mem_iff_getElem] at hmem_row; obtain ⟨idx, hidx_lt, hidx_eq⟩ := hmem_row
  have hpair_eq : rowPair rows[idx] = edgePairNat es[i.val] := by rw [hidx_eq]; rfl
  rw [← hpair_eq]
  by_cases hid_last : rowPair rows[idx] = rowPair rows[k - 1]
  · exact ⟨bestIdx, List.mem_append_right _ (List.mem_singleton_self _), hbi_cp.trans hid_last.symm⟩
  · obtain ⟨q, hq, hqeq⟩ := hprev_cov idx (Nat.le_pred_of_lt hidx_lt) hid_last
    exact ⟨q, List.mem_append_left _ hq, hqeq⟩

private theorem dedup_out_spec_of_scan {n : ℕ} {es : List (IndexedEdge n)}
    {idPref : List (Fin es.length)} {bestIdx : Fin es.length} {p : ℕ × ℕ}
    (hpw_lt : idPref.Pairwise fun q₁ q₂ => pairOrderLT (edgePairNat es[q₁.val])
      (edgePairNat es[q₂.val]))
    (hall_lt : ∀ q ∈ idPref, pairOrderLT (edgePairNat es[q.val]) p)
    (hpref_min : ∀ q ∈ idPref, IsPairMin es (edgePairNat es[q.val]) q)
    (hbi_min : IsPairMin es (edgePairNat es[bestIdx.val]) bestIdx)
    (hbi_cp : edgePairNat es[bestIdx.val] = p)
    (hcov : ∀ i : Fin es.length, es[i.val].u ≠ es[i.val].v →
      ∃ q ∈ idPref ++ [bestIdx], edgePairNat es[q.val] = edgePairNat es[i.val]) :
    let esOut := (idPref ++ [bestIdx]).map fun q => es[q.val]
    esOut.Subperm es ∧
    esOut.map IndexedEdge.toWeighted = dedupSimpleEdges (es.map IndexedEdge.toWeighted) ∧
    ∀ e ∈ es, e.u ≠ e.v →
      ∃ e' ∈ esOut, s(e'.u, e'.v) = s(e.u, e.v) ∧ e'.weight ≤ e.weight := by
  obtain ⟨hpw_full, hmin_full⟩ := idList_step_aux hpw_lt hall_lt hpref_min hbi_cp hbi_min
  have hnd : (idPref ++ [bestIdx]).Nodup :=
    (hpw_full.imp fun {q₁ q₂} h (heq : q₁ = q₂) => pairOrderLT_irrefl _ (heq ▸ h)).nodup
  have hsub_es : ((idPref ++ [bestIdx]).map fun q => es[q.val]).Subperm es := by
    have hm := List.subperm_map (fun q : Fin es.length => es[q])
      (List.subperm_of_subset hnd fun q _ => List.mem_finRange q)
    simpa [List.map_getElem_finRange] using hm
  refine ⟨hsub_es, by simpa only [List.map_map, Function.comp_def] using
    eq_dedupSimpleEdges_of_pairMin hpw_full hmin_full hcov, fun e he hne => ?_⟩
  rw [List.mem_iff_getElem] at he; obtain ⟨i, hi, rfl⟩ := he
  obtain ⟨q, hq, hqeq⟩ := hcov ⟨i, hi⟩ hne
  refine ⟨es[q.val], List.mem_map.mpr ⟨q, hq, rfl⟩, sym2_eq_iff_edgePairNat_eq.mpr hqeq, ?_⟩
  rcases (hmin_full q hq).2.2 ⟨i, hi⟩ hne hqeq.symm with hlt | ⟨heqw, _⟩
  · exact Nat.le_of_lt hlt
  · exact Nat.le_of_eq heqw

private abbrev dedupSortedOutPost (w n maxLen outBase : ℕ) (es : List (IndexedEdge n))
    (out : GraphSlice) (s' : Memory.State) : Prop :=
  out.numVertices = n ∧ out.edgeBase = outBase ∧ s'.frontier = outBase + 4 * maxLen ∧
  Memory.WellFormed w s' ∧ out.numEdges ≤ maxLen ∧
  ∃ esOut : List (IndexedEdge n), esOut.length = out.numEdges ∧ esOut.Subperm es ∧
    HoldsIndexedEdges out.edgeBase esOut s'.mem ∧
    esOut.map IndexedEdge.toWeighted = dedupSimpleEdges (es.map IndexedEdge.toWeighted) ∧
    ∀ e ∈ es, e.u ≠ e.v → ∃ e' ∈ esOut, s(e'.u, e'.v) = s(e.u, e.v) ∧ e'.weight ≤ e.weight

private theorem dedupSortedProg_framed {w n edgeBase sortedBase : ℕ} {es : List (IndexedEdge n)}
    {rows : List (Fin 3 → ℕ)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hrows : HoldsRecords 3 sortedBase rows s.mem)
    (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hk_pos : 0 < rows.length)
    (hed_lt : edgeBase + 4 * es.length ≤ s.frontier)
    (hxs_lt : sortedBase + 3 * rows.length ≤ s.frontier)
    (hfit_k1 : Fits w (rows.length + 1)) (hfit_4k : Fits w (4 * rows.length))
    (hfit : Fits w (s.frontier + 4 * rows.length))
    (hperm : rows.Perm (prepRows es es.length))
    (hsorted : rows.Pairwise pairIdxLT)
    (hcorr : ∀ x ∈ rows, ∃ hlt : x 2 < es.length, es[x 2].u ≠ es[x 2].v ∧
      edgePairNat es[x 2] = (x 0, x 1) ∧ x 0 < x 1) :
    dedupSortedProgSafe w ⟨n, edgeBase, sortedBase, rows.length⟩ s ∧
    Memory.FramedTriple w s (dedupSortedProg ⟨n, edgeBase, sortedBase, rows.length⟩)
      (12 * rows.length + 1) ∅ (dedupSortedOutPost w n rows.length s.frontier es) := by
  let k := rows.length
  let outBase := s.frontier
  let fEnd := outBase + 4 * k
  let s₀ : Memory.State := ⟨s.mem, fEnd⟩
  have hwf₀ : Memory.WellFormed w s₀ := ⟨hfit, fun a => hwf.mem_fits a⟩
  obtain ⟨hidx0_lt, _⟩ := hcorr rows[0] (List.getElem_mem hk_pos)
  obtain ⟨ha0, hb0, hi0⟩ := holdsRecords_zero_mem hrows hk_pos
  obtain ⟨_, _, hw0, _⟩ := hin _ hidx0_lt
  obtain ⟨hsafe_it, hft_scan⟩ := dedupScan_framed h16 hwf₀ hrows hin hk_pos
    (by dsimp only [outBase]; omega) (by dsimp only [outBase]; omega) (le_refl fEnd)
    hfit_k1 hperm hsorted hcorr
  have hsafe_prog : dedupSortedProgSafe w ⟨n, edgeBase, sortedBase, k⟩ s := by
    obtain ⟨_, _, _, htfr_s, _, _, idPref, bestIdx, hst_s, hlen_s, _⟩ :=
      framedTriple_iff_realization.mp hft_scan
    dsimp only [dedupSortedProgSafe]; dsimp only [outBase, fEnd, s₀] at hsafe_it hst_s htfr_s
    have hst0_eq : (⟨1, s.mem sortedBase, s.mem (sortedBase + 1), s.mem (sortedBase + 2),
        s.mem (edgeBase + 4 * s.mem (sortedBase + 2) + 2), 0⟩ : DedupScanState) =
        ⟨1, rows[0] 0, rows[0] 1, rows[0] 2, es[rows[0] 2].weight, 0⟩ := by
      simp only [ha0, hb0, hi0, hw0]
    refine ⟨h16, hfit_k1, hfit_4k, hfit, by dsimp only [k]; omega,
      by dsimp only [k]; rw [hi0]; omega,
      by rw [hst0_eq, hst_s]; exact hfit_k1.of_le (by dsimp only; omega), ?_, ?_,
      hst0_eq ▸ hsafe_it, Nat.succ_le_of_lt hk_pos⟩
    · have := bestIdx.isLt; rw [hst0_eq, hst_s, htfr_s]; dsimp only [k]; omega
    · rw [hst0_eq, hst_s, htfr_s]; dsimp only [k]; omega
  refine ⟨hsafe_prog, ?_⟩
  dsimp only [dedupSortedProg]
  refine ((Memory.FramedTriple.allocBlockDirty_bind hfit
    (?_ : Memory.FramedTriple w s₀ _ (12 * (k - 1) + 8 + 4)
      (Set.Ico outBase (outBase + 4 * k)) (dedupSortedOutPost w n k outBase es))
    ).frame_empty_of_ge_frontier
    (fun a ha => by simp only [Set.mem_Ico] at ha; exact ha.1)).mono
    (by dsimp only [k] at hk_pos ⊢; omega) fun _ _ h => h
  refine Memory.FramedTriple.read_bind (by dsimp only [s₀, fEnd, outBase]; omega) ?_; rw [ha0]
  refine Memory.FramedTriple.read_bind (by dsimp only [s₀, fEnd, outBase]; omega) ?_; rw [hb0]
  refine Memory.FramedTriple.read_bind (by dsimp only [s₀, fEnd, outBase]; omega) ?_; rw [hi0]
  refine Memory.FramedTriple.read_bind (by dsimp only [s₀, fEnd, outBase]; omega) ?_; rw [hw0]
  refine Memory.FramedTriple.bind_same (c₁ := 12 * (k - 1)) (c₂ := 8 + 0) ?_
  refine hft_scan.mono le_rfl fun _ tScan ⟨htfr_s, hwf_s, hin_s, idPref, bestIdx, hst_s,
      hlen_s, hpref_mem, hpw_lt, hall_lt, hpref_min, hbi_min, hbi_cp, hcov_all⟩ => ?_
  rw [hst_s]
  have hcp := copy_append_pref_framed (bestIdx := bestIdx) hwf_s hpref_mem hin_s
    (by dsimp only [outBase]; omega) (by rw [htfr_s]) (by dsimp only [k] at hk_pos hlen_s ⊢; omega)
  refine Memory.FramedTriple.bind_same (c₁ := 8) (c₂ := 0) ?_
  refine hcp.mono le_rfl fun _ _ ⟨htfr_f, hwf_f, hholds_f⟩ => ?_
  obtain ⟨hsub_es, hded_eq, hwit⟩ :=
    dedup_out_spec_of_scan hpw_lt hall_lt hpref_min hbi_min hbi_cp hcov_all
  exact Memory.FramedTriple.pure ⟨rfl, rfl, htfr_f.trans htfr_s, hwf_f,
    by dsimp only [k] at hk_pos hlen_s ⊢; omega, _, by simp, hsub_es, hholds_f, hded_eq, hwit⟩

/-! ## Main program, realization, and specification -/

/-- Remove self-loops and parallel edges (retaining the first minimum-weight edge per unordered
vertex pair in canonical `dedupSimpleEdges` order) from the stride-4 `IndexedEdge` array
described by `g : GraphSlice` in `O(m + n)` memory operations. -/
def dedupSimpleEdgesProg (g : GraphSlice) : Memory.Prog GraphSlice := do
  let norm ← Memory.allocBlockDirty (3 * g.numEdges)
  let stPrep ← iterate dedupPrepStep ⟨g.edgeBase, norm.base⟩ g.numEdges ⟨0, 0⟩
  if stPrep.outCount = 0 then pure ⟨g.numVertices, 0, norm.base⟩
  else do
    let b1 ← countingSortProg ⟨g.numVertices, stPrep.outCount, 3, 0, norm.base⟩
    let b2 ← countingSortProg ⟨g.numVertices, stPrep.outCount, 3, 1, b1.base⟩
    dedupSortedProg ⟨g.numVertices, g.edgeBase, b2.base, stPrep.outCount⟩

private abbrev csOutPost (w n k edgeBase front : ℕ) (rowsOut : List (Fin 3 → ℕ))
    (es : List (IndexedEdge n)) (out : Block) (s' : Memory.State) : Prop :=
  out = ⟨front + n, 3 * k⟩ ∧ s'.frontier = front + n + 3 * k ∧
  Memory.WellFormed w s' ∧ HoldsRecords 3 out.base rowsOut s'.mem ∧
  HoldsIndexedEdges edgeBase es s'.mem

private theorem countingSort_pass_framed {w n edgeBase inBase : ℕ} {es : List (IndexedEdge n)}
    {rowsIn : List (Fin 3 → ℕ)} {t : Memory.State} (keyCol : Fin 3)
    (hwf : Memory.WellFormed w t) (hrows : HoldsRecords 3 inBase rowsIn t.mem)
    (hin : HoldsIndexedEdges edgeBase es t.mem)
    (hed_lt : edgeBase + 4 * es.length ≤ t.frontier)
    (hin_lt : inBase + 3 * rowsIn.length ≤ t.frontier)
    (hbound : ∀ r ∈ rowsIn, r keyCol < n)
    (hfit : Fits w (t.frontier + n + 3 * rowsIn.length)) :
    Memory.FramedTriple w t (countingSortProg ⟨n, rowsIn.length, 3, keyCol.val, inBase⟩)
      (12 * rowsIn.length + 3 * n + 2) ∅
      (csOutPost w n rowsIn.length edgeBase t.frontier
        (countingSortPure n (fun r => r keyCol) rowsIn) es) := by
  have hf := holdsIndexedEdges_frame_mem
    (countingSortProg_spec hwf hrows hin_lt keyCol.isLt hbound hfit) hin
    (Set.empty_disjoint _) hed_lt
  exact hf.mono (by omega) fun _ _ ⟨⟨h1, _, h3, h4, h5⟩, h6⟩ => ⟨h1, h3, h4, h5, h6⟩

private abbrev dedupSimpleEdgesPost (w n m front : ℕ) (es : List (IndexedEdge n))
    (out : GraphSlice) (s' : Memory.State) : Prop :=
  out.numVertices = n ∧ out.edgeBase + 4 * out.numEdges ≤ s'.frontier ∧
  s'.frontier ≤ front + (13 * m + 2 * n) ∧ Memory.WellFormed w s' ∧
  ∃ esOut : List (IndexedEdge n), esOut.length = out.numEdges ∧ esOut.Subperm es ∧
    HoldsIndexedEdges out.edgeBase esOut s'.mem ∧
    esOut.map IndexedEdge.toWeighted = dedupSimpleEdges (es.map IndexedEdge.toWeighted) ∧
    IsSimple (edgeEnds (esOut.map IndexedEdge.toWeighted)) ∧
    ∀ e ∈ es, e.u ≠ e.v → ∃ e' ∈ esOut, s(e'.u, e'.v) = s(e.u, e.v) ∧ e'.weight ≤ e.weight

private abbrev dedupSimpleEdgesPre (w : ℕ) (g : GraphSlice) (s : Memory.State) : Prop :=
  let normBase := s.frontier; let s₀ : Memory.State := ⟨s.mem, normBase + 3 * g.numEdges⟩
  let itPrep := iterate dedupPrepStep ⟨g.edgeBase, normBase⟩ g.numEdges ⟨0, 0⟩
  let stPrep := (Memory.spec 0).clientResult s₀ itPrep
  let s₁ := (Memory.spec 0).clientState s₀ itPrep
  let cs0 := countingSortProg ⟨g.numVertices, stPrep.outCount, 3, 0, normBase⟩
  let b1 := (Memory.spec 0).clientResult s₁ cs0
  let s₂ := (Memory.spec 0).clientState s₁ cs0
  let cs1 := countingSortProg ⟨g.numVertices, stPrep.outCount, 3, 1, b1.base⟩
  let b2 := (Memory.spec 0).clientResult s₂ cs1
  let s₃ := (Memory.spec 0).clientState s₂ cs1
  Fits w 16 ∧ Fits w (3 * g.numEdges) ∧ Fits w (normBase + 3 * g.numEdges) ∧
    iterationSafe dedupPrepStep dedupPrepStepSafe w ⟨g.edgeBase, normBase⟩
      g.numEdges ⟨0, 0⟩ s₀ ∧
    (stPrep.outCount ≠ 0 →
      (normBase + 3 * stPrep.outCount ≤ s₁.frontier ∧
        Fits w (s₁.frontier + g.numVertices + 3 * stPrep.outCount) ∧
        ∀ i < stPrep.outCount, s₁.mem (normBase + 3 * i + 0) < g.numVertices) ∧
      (b1.base + 3 * stPrep.outCount ≤ s₂.frontier ∧
        Fits w (s₂.frontier + g.numVertices + 3 * stPrep.outCount) ∧
        ∀ i < stPrep.outCount, s₂.mem (b1.base + 3 * i + 1) < g.numVertices) ∧
      dedupSortedProgSafe w ⟨g.numVertices, g.edgeBase, b2.base, stPrep.outCount⟩ s₃)

private theorem dedupTail_framed {w n edgeBase normBase : ℕ} {es : List (IndexedEdge n)}
    {t : Memory.State}
    (h16 : Fits w 16) (htwf : Memory.WellFormed w t)
    (htfr : t.frontier = normBase + 3 * es.length)
    (htrows : HoldsRecords 3 normBase (prepRows es es.length) t.mem)
    (htin : HoldsIndexedEdges edgeBase es t.mem)
    (hed_lt : edgeBase + 4 * es.length ≤ normBase)
    (hfit : Fits w (normBase + (13 * es.length + 2 * n)))
    (hk_pos : 0 < (prepRows es es.length).length) :
    let m := es.length
    let k := (prepRows es m).length
    let b1 := (Memory.spec 0).clientResult t (countingSortProg ⟨n, k, 3, 0, normBase⟩)
    let s₂ := (Memory.spec 0).clientState t (countingSortProg ⟨n, k, 3, 0, normBase⟩)
    let b2 := (Memory.spec 0).clientResult s₂ (countingSortProg ⟨n, k, 3, 1, b1.base⟩)
    let s₃ := (Memory.spec 0).clientState s₂ (countingSortProg ⟨n, k, 3, 1, b1.base⟩)
    (normBase + 3 * k ≤ t.frontier ∧ Fits w (t.frontier + n + 3 * k) ∧
      ∀ i < k, t.mem (normBase + 3 * i + 0) < n) ∧
    (b1.base + 3 * k ≤ s₂.frontier ∧ Fits w (s₂.frontier + n + 3 * k) ∧
      ∀ i < k, s₂.mem (b1.base + 3 * i + 1) < n) ∧
    dedupSortedProgSafe w ⟨n, edgeBase, b2.base, k⟩ s₃ ∧
    Memory.FramedTriple w t
      (countingSortProg ⟨n, k, 3, 0, normBase⟩ >>= fun b1' =>
        countingSortProg ⟨n, k, 3, 1, b1'.base⟩ >>= fun b2' =>
          dedupSortedProg ⟨n, edgeBase, b2'.base, k⟩)
      ((12 * k + 3 * n + 2) + ((12 * k + 3 * n + 2) + (12 * k + 1))) ∅
      (dedupSimpleEdgesPost w n m normBase es) := by
  have hprep_le : (prepRows es es.length).length ≤ es.length := prepRows_length_le es es.length
  let m := es.length; let rows₀ := prepRows es m; let k := rows₀.length
  have hk_es : k ≤ es.length := hprep_le
  have hbound₀ : ∀ r ∈ rows₀, r ⟨0, by decide⟩ < n := fun r hr => (prepRows_mem hr).2.2.2.2.1
  let rows₁ := countingSortPure n (fun r => r ⟨0, by decide⟩) rows₀
  have hperm₁ : rows₁.Perm rows₀ := countingSortPure_perm n _ rows₀ hbound₀
  have hlen₁ : rows₁.length = k := hperm₁.length_eq
  have hbound₁ : ∀ r ∈ rows₁, r ⟨1, by decide⟩ < n := fun r hr =>
    (prepRows_mem (hperm₁.subset hr)).2.2.2.2.2
  let rows₂ := countingSortPure n (fun r => r ⟨1, by decide⟩) rows₁
  have hperm₂₀ : rows₂.Perm rows₀ := (countingSortPure_perm n _ rows₁ hbound₁).trans hperm₁
  have hlen₂ : rows₂.length = k := hperm₂₀.length_eq
  have hsorted₂ : rows₂.Pairwise pairIdxLT := by
    refine List.Pairwise.imp (fun {r₁ r₂} h => ?_) (countingSortPure_stable n
      (fun r => r ⟨1, by decide⟩) (countingSortPure_stable n (fun r => r ⟨0, by decide⟩)
        (prepRows_pairwise_idx es)))
    rcases h with h | ⟨h1, h0 | ⟨h2, h3⟩⟩ <;> [exact Or.inl (Or.inl h);
      exact Or.inl (Or.inr ⟨h1, h0⟩); exact Or.inr ⟨Prod.ext h2 h1, h3⟩]
  have hcorr₂ : ∀ x ∈ rows₂, ∃ hlt : x 2 < m, es[x 2].u ≠ es[x 2].v ∧
      edgePairNat es[x 2] = (x 0, x 1) ∧ x 0 < x 1 := fun x hx => by
    obtain ⟨hlt, hne, hcp, h01, _, _⟩ := prepRows_mem (hperm₂₀.subset hx)
    exact ⟨hlt, hne, hcp, h01⟩
  have hft_cs1 : Memory.FramedTriple w t (countingSortProg ⟨n, k, 3, 0, normBase⟩)
      (12 * k + 3 * n + 2) ∅ (csOutPost w n k edgeBase t.frontier rows₁ es) := by
    simpa only [k] using countingSort_pass_framed ⟨0, by decide⟩ htwf htrows htin
      (by rw [htfr]; omega) (by rw [htfr]; omega)
      hbound₀ (by rw [htfr]; exact hfit.of_le (by omega))
  have hcs2_of : ∀ b1Base (s2' : Memory.State), b1Base = t.frontier + n →
      s2'.frontier = t.frontier + n + 3 * k → Memory.WellFormed w s2' →
      HoldsRecords 3 b1Base rows₁ s2'.mem → HoldsIndexedEdges edgeBase es s2'.mem →
      Memory.FramedTriple w s2' (countingSortProg ⟨n, k, 3, 1, b1Base⟩)
        (12 * k + 3 * n + 2) ∅ (csOutPost w n k edgeBase s2'.frontier rows₂ es) :=
    fun b1Base s2' hb1 hs2 hw2 hr2 hi2 => by
      simpa only [hlen₁] using countingSort_pass_framed ⟨1, by decide⟩ hw2 hr2 hi2
        (by rw [hs2, htfr]; omega) (by rw [hb1, hs2, hlen₁]) hbound₁
        (by rw [hs2, htfr, hlen₁]; exact hfit.of_le (by have := hk_es; omega))
  have hds_of : ∀ b2Base (s3' : Memory.State), b2Base = t.frontier + n + 3 * k + n →
      s3'.frontier = t.frontier + n + 3 * k + n + 3 * k → Memory.WellFormed w s3' →
      HoldsRecords 3 b2Base rows₂ s3'.mem → HoldsIndexedEdges edgeBase es s3'.mem →
      dedupSortedProgSafe w ⟨n, edgeBase, b2Base, k⟩ s3' ∧
      Memory.FramedTriple w s3' (dedupSortedProg ⟨n, edgeBase, b2Base, k⟩) (12 * k + 1) ∅
        (dedupSortedOutPost w n k s3'.frontier es) := fun b2Base s3' hb2 hs3 hw3 hr3 hi3 => by
    simpa only [hlen₂] using dedupSortedProg_framed h16 hw3 hr3 hi3 (hlen₂ ▸ hk_pos)
      (by rw [hs3, htfr]; omega) (by rw [hb2, hs3, hlen₂])
      (by rw [hlen₂]; exact hfit.of_le (by have := hk_es; omega))
      (by rw [hlen₂]; exact hfit.of_le (by have := hk_es; omega))
      (by rw [hs3, htfr, hlen₂]; exact hfit.of_le (by have := hk_es; omega)) hperm₂₀ hsorted₂ hcorr₂
  set b1 := (Memory.spec 0).clientResult t (countingSortProg ⟨n, k, 3, 0, normBase⟩)
  set s₂ := (Memory.spec 0).clientState t (countingSortProg ⟨n, k, 3, 0, normBase⟩)
  obtain ⟨_, _, _, hb1_eq, hs2_fr, hwf₂, hrows₂, hin_s2⟩ := framedTriple_iff_realization.mp hft_cs1
  set b2 := (Memory.spec 0).clientResult s₂ (countingSortProg ⟨n, k, 3, 1, b1.base⟩)
  set s₃ := (Memory.spec 0).clientState s₂ (countingSortProg ⟨n, k, 3, 1, b1.base⟩)
  obtain ⟨_, _, _, hb2_eq, hs3_fr, hwf₃, hrows₃, hin_s3⟩ := framedTriple_iff_realization.mp
    (hcs2_of b1.base s₂ (by dsimp only [b1]; rw [hb1_eq]) hs2_fr hwf₂ hrows₂ hin_s2)
  refine ⟨⟨by rw [htfr]; omega, by rw [htfr]; exact hfit.of_le (by omega),
    fun i hi => by rw [htrows i hi ⟨0, by decide⟩]; exact hbound₀ _ (List.getElem_mem hi)⟩,
    ⟨by rw [hb1_eq, hs2_fr],
      by rw [hs2_fr, htfr]; exact hfit.of_le (by have := hk_es; omega),
      fun i hi => by rw [hrows₂ i (hlen₁ ▸ hi) ⟨1, by decide⟩]
                     exact hbound₁ _ (List.getElem_mem (hlen₁ ▸ hi))⟩,
    (hds_of b2.base s₃ (by dsimp only [b2, s₂]; rw [hb2_eq, hs2_fr])
      (by dsimp only [s₃, s₂]; rw [hs3_fr, hs2_fr]) hwf₃ hrows₃ hin_s3).1, ?_⟩
  refine Memory.FramedTriple.bind_same (c₁ := 12 * k + 3 * n + 2)
    (c₂ := (12 * k + 3 * n + 2) + (12 * k + 1)) ?_
  refine hft_cs1.mono le_rfl fun b1' s2' ⟨hb1'_eq, hs2'_fr, hwf2', hrows2', hin2'⟩ => ?_
  refine Memory.FramedTriple.bind_same (c₁ := 12 * k + 3 * n + 2) (c₂ := 12 * k + 1) ?_
  refine (hcs2_of b1'.base s2' (by rw [hb1'_eq]) hs2'_fr hwf2' hrows2' hin2').mono le_rfl
    fun b2' s3' ⟨hb2'_eq, hs3'_fr, hwf3', hrows3', hin3'⟩ =>
    (hds_of b2'.base s3' (by rw [hb2'_eq, hs2'_fr]) (by rw [hs3'_fr, hs2'_fr])
      hwf3' hrows3' hin3').2.mono le_rfl fun _ _ ⟨hvn, heb, hs'fr, hwf', _, esOut, hlen_out,
        hsub_out, hholds_out, hded_out, hwit_out⟩ =>
      ⟨hvn, by rw [heb, hs'fr]; omega, by rw [hs'fr, hs3'_fr, hs2'_fr, htfr]; omega, hwf',
        esOut, hlen_out, hsub_out, hholds_out, hded_out,
        hded_out ▸ dedupSimpleEdges_isSimple _, hwit_out⟩

private theorem dedupSimpleEdgesProg_word_spec {w n edgeBase : ℕ} {es : List (IndexedEdge n)}
    {s : Memory.State} (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges edgeBase es s.mem) (hin_lt : edgeBase + 4 * es.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + (13 * es.length + 2 * n))) :
    dedupSimpleEdgesPre w ⟨n, es.length, edgeBase⟩ s ∧
    Memory.FramedTriple w s (dedupSimpleEdgesProg ⟨n, es.length, edgeBase⟩)
      (41 * es.length + 6 * n + 6) ∅ (dedupSimpleEdgesPost w n es.length s.frontier es) := by
  let m := es.length; let normBase := s.frontier; let s₀ : Memory.State := ⟨s.mem, normBase + 3 * m⟩
  let rows₀ := prepRows es m; let k := rows₀.length
  have hk_le : k ≤ m := prepRows_length_le es m
  have hfit_m1 : Fits w (m + 1) := by
    rcases Nat.eq_zero_or_pos m with hm0 | _
    · exact hm0 ▸ h16.of_le (by decide)
    · exact hfit.of_le (by omega)
  have hfit_3m : Fits w (s.frontier + 3 * m) := hfit.of_le (by omega)
  have hwf₀ : Memory.WellFormed w s₀ := ⟨hfit_3m, fun a => hwf.mem_fits a⟩
  obtain ⟨hsafe_p, hft_p⟩ := dedupPrep_framed h16 hwf₀ hin (by dsimp only [s₀]; omega)
    (le_refl (normBase + 3 * m)) hin_lt hfit_m1
  let itPrep := iterate dedupPrepStep ⟨edgeBase, normBase⟩ m ⟨0, 0⟩
  obtain ⟨_, _, hmod_p, hres_p, hfr_p, hwf_p, hrows_p⟩ := framedTriple_iff_realization.mp hft_p
  set stPrep := (Memory.spec 0).clientResult s₀ itPrep
  set s₁ := (Memory.spec 0).clientState s₀ itPrep
  have hst_count : stPrep.outCount = k := by rw [hres_p]
  have hin_s1 : HoldsIndexedEdges edgeBase es s₁.mem :=
    hin.congr fun x _ hx => hmod_p.mem_eq_of_not_mem (by dsimp only [s₀]; omega)
      (by simp only [Set.mem_Ico]; omega)
  have hwrap : ∀ c, c + 1 ≤ 41 * m + 6 * n + 6 →
      Memory.FramedTriple w s₀
        (itPrep >>= fun st => if st.outCount = 0 then pure ⟨n, 0, normBase⟩
          else countingSortProg ⟨n, st.outCount, 3, 0, normBase⟩ >>= fun b1' =>
            countingSortProg ⟨n, st.outCount, 3, 1, b1'.base⟩ >>= fun b2' =>
              dedupSortedProg ⟨n, edgeBase, b2'.base, st.outCount⟩)
        c (Set.Ico normBase (normBase + 3 * m)) (dedupSimpleEdgesPost w n m s.frontier es) →
      Memory.FramedTriple w s (dedupSimpleEdgesProg ⟨n, m, edgeBase⟩)
        (41 * m + 6 * n + 6) ∅ (dedupSimpleEdgesPost w n m s.frontier es) := fun c hc hp =>
    ((Memory.FramedTriple.allocBlockDirty_bind hfit_3m hp).frame_empty_of_ge_frontier
      (fun a ha => by simp only [Set.mem_Ico, normBase] at ha; exact ha.1)).mono hc fun _ _ h => h
  by_cases hk0 : k = 0
  · have hded_nil := dedupSimpleEdges_nil_of_prepRows_empty hk0
    have hnowit : ∀ e ∈ es, e.u ≠ e.v → ∃ e' ∈ ([] : List (IndexedEdge n)),
        s(e'.u, e'.v) = s(e.u, e.v) ∧ e'.weight ≤ e.weight := fun e he hne => by
      rw [List.mem_iff_getElem] at he; obtain ⟨i, hi, rfl⟩ := he
      have := List.length_pos_of_mem (mem_prepRows_of_ne ⟨i, hi⟩ hne)
      dsimp only [k, rows₀, m] at hk0; omega
    refine ⟨⟨h16, hfit.of_le (by dsimp only; omega), hfit_3m, hsafe_p,
      fun hc => absurd (hst_count.trans hk0) hc⟩, hwrap (5 * m) (by omega) ?_⟩
    refine (Memory.FramedTriple.bind_same (c₁ := 5 * m) (c₂ := 0) ?_).mono le_rfl fun _ _ h => h
    refine hft_p.mono le_rfl fun st t ⟨hst, htfr, htwf, _⟩ => ?_
    have hcnt0 : st.outCount = 0 := by rw [hst]; exact hk0
    simp only [hcnt0, ↓reduceIte]
    exact Memory.FramedTriple.pure ⟨rfl, by rw [htfr]; dsimp only [s₀, normBase]; omega,
      by rw [htfr]; dsimp only [s₀, normBase]; omega, htwf, [], rfl, List.nil_subperm,
      fun _ h => absurd h (Nat.not_lt_zero _), hded_nil,
      hded_nil ▸ dedupSimpleEdges_isSimple _, hnowit⟩
  · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
    obtain ⟨hs1, hs2, hs3, _⟩ := dedupTail_framed h16 hwf_p hfr_p hrows_p hin_s1 hin_lt hfit hk_pos
    refine ⟨⟨h16, hfit.of_le (by dsimp only; omega), hfit_3m, hsafe_p,
      fun _ => ⟨hst_count ▸ hs1, hst_count ▸ hs2, hst_count ▸ hs3⟩⟩,
      hwrap (5 * m + ((12 * k + 3 * n + 2) + ((12 * k + 3 * n + 2) + (12 * k + 1))))
        (by have := hk_le; omega) ?_⟩
    refine Memory.FramedTriple.bind_same (c₁ := 5 * m)
      (c₂ := (12 * k + 3 * n + 2) + ((12 * k + 3 * n + 2) + (12 * k + 1))) ?_
    refine (holdsIndexedEdges_frame_mem hft_p hin (Set.disjoint_left.mpr fun a ha hb => by
      simp only [Set.mem_Ico] at ha hb; dsimp only [normBase, m] at ha hb; omega)
      (by dsimp only [s₀, normBase, m]; omega)).mono le_rfl
      fun st t ⟨⟨hst, htfr, htwf, htrows⟩, htin⟩ => ?_
    have hst_eq : st = ⟨m, k⟩ := hst; rw [hst_eq]; dsimp only; simp only [hk0, ↓reduceIte]
    exact (dedupTail_framed h16 htwf htfr htrows htin hin_lt hfit hk_pos).2.2.2.frame_mono
      (Set.empty_subset _)

/-- Uniform `Realizes .exact` certificate for `dedupSimpleEdgesProg` with `work = 0`. -/
theorem realizes_dedupSimpleEdgesProg : Realizes .exact
    dedupSimpleEdgesProg WordEncoding.encode WordEncoding.encode
    (fun w g s => Fits w 16 ∧ g.edgeBase + 4 * g.numEdges ≤ s.frontier ∧
      Fits w (s.frontier + (13 * g.numEdges + 2 * g.numVertices)) ∧
      ∀ j < g.numEdges,
        s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
        s.mem (g.edgeBase + 4 * j + 1) < g.numVertices)
    (fun _ _ => 0) := by
  have hraw : Realizes .exact dedupSimpleEdgesProg WordEncoding.encode WordEncoding.encode
      dedupSimpleEdgesPre (fun _ _ => 0) := by
    unfold dedupSimpleEdgesProg
    realize [realizes_allocBlockDirty, realizes_dedupPrepStep, realizes_countingSortProg,
      realizes_dedupSortedProg]
    all_goals
      try simp only [Memory.clientResult_allocBlockDirty] at *
      rcases h with ⟨h16, h3m, hnm, hsafe_p, hnz⟩
      have hfront := hmem.frontier_fits
      first
      | decide | exact h3m | exact iterationSafe_imp hsafe_p (fun _ => rfl) (fun _ _ hs => hs)
      | exact (hnz hc).1.1 | exact (hnz hc).1.2.1 | exact (hnz hc).1.2.2
      | exact (hnz hc).2.1.1 | exact (hnz hc).2.1.2.1 | exact (hnz hc).2.1.2.2
      | exact (hnz hc).2.2 | fits [h3m, hnm]
  refine hraw.consequence (fun w ⟨_, _, _⟩ s _ hmem ⟨h16, hin_lt, hfit, hedges⟩ => ?_)
    (fun _ _ => le_rfl)
  obtain ⟨es, hes_len, hin⟩ := exists_indexedEdges_of_mem_lt hedges
  dsimp only at hes_len hin_lt hfit
  rw [← hes_len] at hin_lt hfit ⊢; exact (dedupSimpleEdgesProg_word_spec h16 hmem hin hin_lt hfit).1

/-- Framed `O(m + n)` specification for `dedupSimpleEdgesProg`: removes self-loops and duplicate
parallel edges (retaining the first minimum-weight edge per unordered vertex pair matching
`dedupSimpleEdges`) from the `IndexedEdge` array at `edgeBase`, leaving all cells below
`s.frontier` untouched, in at most `41 * es.length + 6 * n + 6` memory operations. -/
theorem dedupSimpleEdgesProg_spec {w n edgeBase : ℕ} {es : List (IndexedEdge n)}
    {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hin_lt : edgeBase + 4 * es.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + (13 * es.length + 2 * n))) :
    Memory.FramedTriple w s (dedupSimpleEdgesProg ⟨n, es.length, edgeBase⟩)
      (41 * es.length + 6 * n + 6) ∅ fun out s' =>
        out.numVertices = n ∧
        out.edgeBase + 4 * out.numEdges ≤ s'.frontier ∧
        s'.frontier ≤ s.frontier + (13 * es.length + 2 * n) ∧
        Memory.WellFormed w s' ∧
        ∃ esOut : List (IndexedEdge n),
          esOut.length = out.numEdges ∧
          esOut.Subperm es ∧
          HoldsIndexedEdges out.edgeBase esOut s'.mem ∧
          esOut.map IndexedEdge.toWeighted = dedupSimpleEdges (es.map IndexedEdge.toWeighted) ∧
          IsSimple (edgeEnds (esOut.map IndexedEdge.toWeighted)) ∧
          ∀ e ∈ es, e.u ≠ e.v →
            ∃ e' ∈ esOut, s(e'.u, e'.v) = s(e.u, e.v) ∧ e'.weight ≤ e.weight :=
  (dedupSimpleEdgesProg_word_spec h16 hwf hin hin_lt hfit).2

end Cslib.Algorithms.WordRAM.MinimumSpanningForest
