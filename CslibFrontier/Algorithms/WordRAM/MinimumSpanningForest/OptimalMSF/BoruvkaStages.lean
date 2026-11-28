/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.Dedup
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.Boruvka
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.Components
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSF.BaseOps
import CslibFrontier.Foundations.Data.List.Subperm
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.ValidProg

/-!
# Initial Graph Preprocessing and Borůvka Contraction Stages for Optimal MSF

Word-RAM preprocessing and 3-round Borůvka contraction toward Section 2.1 (p. 18), Section 5
(pp. 23–24), and Theorem 5.8 (Section 5.1, p. 27) of [PettieRamachandran2002] (#8624).
Pettie and Ramachandran (Section 2.1, p. 18; Section 5, pp. 23–24) use 2-round `Boruvka2` on
connected inputs with `ε = 1 / 8`, whereas `boruvkaThreeStageProg` runs three contraction rounds
for an `8×` vertex reduction matching `Partition`'s fixed `ε = 1 / 16` (`partRankThreshold = 8`)
on general non-isolated multigraphs (`n ≤ 2m`):

- `MSFLiftInv` and `MSFLiftInv.sum_le`: loop invariant tracking accumulated selected edge IDs and
  remaining contracted edges, guaranteeing that any MSF of the contracted graph lifts back to an
  MSF of the original input edge list.
- `InitPreprocessArgs`, `initPreprocessProg`: materializes stride-3 raw input edges into indexed
  edges, removes self-loops and parallel edges via `dedupSimpleEdgesProg`, and compacts isolated
  vertices via `compactVerticesProg`, returning a simple non-isolated `GraphSlice`.
- `BoruvkaStageArgs`, `BoruvkaStageResult`, `boruvkaThreeStageProg`: 3-round Borůvka contraction
  stage appending selected original edge IDs to the accumulated MSF array and reducing the active
  vertex count by at least a factor of `8` (`8 * res.numVertices ≤ nCur`).

## Main definitions

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.MSFLiftInv`: invariant preserving MSF liftability
  across Borůvka contraction stages.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.InitPreprocessArgs`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.encInitPreprocessArgs`: 3-word argument bundle
  for `initPreprocessProg`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.initPreprocessProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.initPreprocessProgSafe`: initial indexing,
  deduplication, and vertex compaction pipeline.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.BoruvkaStageArgs`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.encBoruvkaStageArgs`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.BoruvkaStageResult`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.encBoruvkaStageResult`: flat 5-word input and
  4-word result bundles for `boruvkaThreeStageProg`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.boruvkaThreeStageProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.boruvkaThreeStageProgSafe`: three-round Borůvka
  contraction stage and its closed-form Word-RAM safety domain.

## Main results

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.MSFLiftInv.sum_le`: total edge budget bound
  `accIds.length + esCur.length ≤ es.length`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_initPreprocessProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.initPreprocessProg_spec`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.initPreprocessProg_numVertices_le`:
  Word-RAM realization, framed `O(m + n)` spec, and vertex bound for `initPreprocessProg`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_boruvkaThreeStageProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.boruvkaThreeStageProg_spec`: Word-RAM realization
  and framed `O(m + n)` specification for `boruvkaThreeStageProg` (`8 * res.numVertices ≤ nCur`).

## References

* [Pettie and Ramachandran, *An Optimal Minimum Spanning Tree Algorithm*,
  Journal of the ACM 49(1), 2002][PettieRamachandran2002], Section 2.1 (p. 18),
  Section 5 (pp. 23–24), and Section 5.1 (pp. 25–27)
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Algorithms.WordRAM.Kruskal
open Cslib.Query.MinimumSpanningForest

/-! ## Section 1: Invariant and Graph-Lifting Helpers -/

private theorem mem_mapIdx_eq {n : ℕ} {es : List (WeightedEdge n ℕ)} {e : IndexedEdge n}
    (he : e ∈ es.mapIdx fun i x => ⟨x.u, x.v, x.weight, i⟩) :
    ∃ _ : e.id < es.length, e.toWeighted = es[e.id] := by
  rw [List.mem_mapIdx] at he
  obtain ⟨i, hi, rfl⟩ := he
  exact ⟨hi, rfl⟩

private theorem mapIdx_id_eq_range {n : ℕ} (es : List (WeightedEdge n ℕ)) :
    (es.mapIdx fun i x => (⟨x.u, x.v, x.weight, i⟩ : IndexedEdge n)).map IndexedEdge.id =
      List.range es.length := by
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    simp

private theorem mapIdx_toWeighted {n : ℕ} (es : List (WeightedEdge n ℕ)) :
    (es.mapIdx fun i x => (⟨x.u, x.v, x.weight, i⟩ : IndexedEdge n)).map
      IndexedEdge.toWeighted = es := by
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    simp [IndexedEdge.toWeighted]

/-- Loop invariant tracking accumulated original MSF edge indices `accIds` and remaining
contracted edges `esCur`, ensuring any MSF of `esCur` lifts back to an MSF of `es`. -/
@[expose] def MSFLiftInv {n nCur : ℕ} (es : List (WeightedEdge n ℕ))
    (accIds : List (Fin es.length)) (esCur : List (IndexedEdge nCur)) : Prop :=
  accIds.Nodup ∧
  (esCur.map IndexedEdge.id).Nodup ∧
  (∀ e ∈ esCur, e.id < es.length) ∧
  (∀ i ∈ accIds, ∀ e ∈ esCur, e.id ≠ i.val) ∧
  ∀ L : List (IndexedEdge nCur),
    L.Subperm esCur →
    IsMinSpanningForest (esCur.map IndexedEdge.toWeighted) (L.map IndexedEdge.toWeighted) →
    ∃ remIds : List (Fin es.length),
      remIds.map Fin.val = L.map IndexedEdge.id ∧
      IsMinSpanningForest es ((accIds ++ remIds).map fun i => es[i.val])

/-- Total count of accumulated selected IDs and remaining edges never exceeds `es.length`. -/
theorem MSFLiftInv.sum_le {n nCur : ℕ} {es : List (WeightedEdge n ℕ)}
    {accIds : List (Fin es.length)} {esCur : List (IndexedEdge nCur)}
    (h : MSFLiftInv es accIds esCur) : accIds.length + esCur.length ≤ es.length := by
  let xs : List ℕ := accIds.map Fin.val ++ esCur.map IndexedEdge.id
  have hnodup_acc : (accIds.map Fin.val).Nodup := h.1.map Fin.val_injective
  have hdisj : ∀ a ∈ accIds.map Fin.val, ∀ b ∈ esCur.map IndexedEdge.id, a ≠ b := by
    intro a ha b hb heq
    subst heq
    rw [List.mem_map] at ha hb
    obtain ⟨i, hi, rfl⟩ := ha
    obtain ⟨e, he, heq2⟩ := hb
    exact h.2.2.2.1 i hi e he heq2
  have hnodup : xs.Nodup := List.nodup_append.mpr ⟨hnodup_acc, h.2.1, hdisj⟩
  have hsub : ∀ x ∈ xs, x ∈ List.range es.length := by
    intro x hx
    rw [List.mem_range]
    rcases List.mem_append.mp hx with hx1 | hx2
    · rw [List.mem_map] at hx1
      obtain ⟨i, _, rfl⟩ := hx1
      exact i.isLt
    · rw [List.mem_map] at hx2
      obtain ⟨e, he, rfl⟩ := hx2
      exact h.2.2.1 e he
  have hsp : xs.Subperm (List.range es.length) := List.subperm_of_subset hnodup hsub
  have hlen := hsp.length_le
  simp only [xs, List.length_append, List.length_map, List.length_range] at hlen
  exact hlen

private theorem nodup_map_id_of_nodup {n : ℕ} {es : List (IndexedEdge n)}
    (hnd : (es.map IndexedEdge.id).Nodup) {idxs : List (Fin es.length)} (hidxs : idxs.Nodup) :
    (idxs.map fun i => (es[i.val]).id).Nodup := by
  refine hidxs.map fun x y heq => Fin.ext (hnd.eq_of_getElem_eq
    (by simp [x.isLt]) (by simp [y.isLt]) ?_)
  simpa only [List.getElem_map] using heq

/-! ## Section 2: Initial Indexing, Deduplication, and Compaction (`initPreprocessProg`) -/

/-- Input arguments for `initPreprocessProg`: vertex count, raw edge count, and stride-3 raw
edge array base address. -/
structure InitPreprocessArgs where
  /-- Number of input vertices `n`. -/
  numVertices : ℕ
  /-- Number of stride-3 raw input edges `m`. -/
  numEdges : ℕ
  /-- Base address of the stride-3 raw edge array `[u, v, weight, ...]`. -/
  inBase : ℕ
  deriving DecidableEq

/-- Faithful 3-word encoding of `InitPreprocessArgs` as `[numVertices, numEdges, inBase]`. -/
word_enc_structure encInitPreprocessArgs : InitPreprocessArgs where
  numVertices : wordWords,
  numEdges : wordWords,
  inBase : wordWords

instance : WordEncoding InitPreprocessArgs := ⟨3, encInitPreprocessArgs⟩

/-- Materialize stride-3 raw input edges at `a.inBase` into indexed edges, remove self-loops and
parallel edges via `dedupSimpleEdgesProg`, and compact isolated vertices via `compactVerticesProg`,
returning the compacted simple `GraphSlice`. -/
def initPreprocessProg (a : InitPreprocessArgs) : Memory.Prog GraphSlice := do
  let eb1 ← initIndexedEdges a.inBase a.numEdges
  let dd ← dedupSimpleEdgesProg ⟨a.numVertices, a.numEdges, eb1⟩
  let cp ← compactVerticesProg dd
  pure ⟨cp.numVertices, dd.numEdges, cp.edgeBase⟩

/-- Closed-form Word-RAM safety domain for `initPreprocessProg`. -/
@[expose] def initPreprocessProgSafe (w : ℕ) (a : InitPreprocessArgs)
    (s : Memory.State) : Prop :=
  Fits w 16 ∧ a.inBase + 3 * a.numEdges ≤ s.frontier ∧
    Fits w (s.frontier + (21 * a.numEdges + 3 * a.numVertices + 1)) ∧
    ∀ j < a.numEdges,
      s.mem (a.inBase + 3 * j) < a.numVertices ∧
      s.mem (a.inBase + 3 * j + 1) < a.numVertices

private theorem exists_rawEdges_of_initPreprocessSafe {w : ℕ} {a : InitPreprocessArgs}
    {s : Memory.State} (hsafe : initPreprocessProgSafe w a s) :
    ∃ rawEs : List (WeightedEdge a.numVertices ℕ),
      rawEs.length = a.numEdges ∧ HoldsEdges a.inBase rawEs s.mem := by
  rcases a with ⟨n, m, inBase⟩
  obtain ⟨_, _, _, hedges⟩ := hsafe
  let rawEs : List (WeightedEdge n ℕ) := List.ofFn fun i : Fin m =>
    ⟨⟨s.mem (inBase + 3 * i.val), (hedges i.val i.isLt).1⟩,
      ⟨s.mem (inBase + 3 * i.val + 1), (hedges i.val i.isLt).2⟩,
      s.mem (inBase + 3 * i.val + 2)⟩
  exact ⟨rawEs, List.length_ofFn, fun i hi => by simp [rawEs]⟩

private theorem initPreprocess_word_post {w : ℕ} {a : InitPreprocessArgs} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hsafe : initPreprocessProgSafe w a s) :
    let eb1 := (Memory.spec 0).clientResult s (initIndexedEdges a.inBase a.numEdges)
    let s₁ := (Memory.spec 0).clientState s (initIndexedEdges a.inBase a.numEdges)
    let g₁ : GraphSlice := ⟨a.numVertices, a.numEdges, eb1⟩
    let dd := (Memory.spec 0).clientResult s₁ (dedupSimpleEdgesProg g₁)
    let s₂ := (Memory.spec 0).clientState s₁ (dedupSimpleEdgesProg g₁)
    (eb1 + 4 * a.numEdges ≤ s₁.frontier ∧
      Fits w (s₁.frontier + (13 * a.numEdges + 2 * a.numVertices)) ∧
      ∀ j < a.numEdges, s₁.mem (eb1 + 4 * j) < a.numVertices ∧
        s₁.mem (eb1 + 4 * j + 1) < a.numVertices) ∧
    (dd.edgeBase + 4 * dd.numEdges ≤ s₂.frontier ∧
      Fits w (s₂.frontier + (dd.numVertices + 4 * dd.numEdges + 1)) ∧
      ∀ j < dd.numEdges, s₂.mem (dd.edgeBase + 4 * j) < dd.numVertices ∧
        s₂.mem (dd.edgeBase + 4 * j + 1) < dd.numVertices) := by
  rcases a with ⟨n, m, inBase⟩
  obtain ⟨rawEs, hlen, hraw⟩ := exists_rawEdges_of_initPreprocessSafe hsafe
  obtain ⟨h16, hin, hfit, _⟩ := hsafe
  dsimp only at hlen hraw hin hfit ⊢
  have h1 := framedTriple_iff_realization.mp
    (initIndexedEdges_spec h16 hwf hraw (by simpa [hlen] using hin)
      (by simpa [hlen] using hfit.of_le (by omega)))
  rw [hlen] at h1
  obtain ⟨_, _, _, heb1, hs1_fr, hwf1, hidx1⟩ := h1
  set eb1 := (Memory.spec 0).clientResult s (initIndexedEdges inBase m)
  set s₁ := (Memory.spec 0).clientState s (initIndexedEdges inBase m)
  let es1 : List (IndexedEdge n) := rawEs.mapIdx fun i e => ⟨e.u, e.v, e.weight, i⟩
  have hlen1 : es1.length = m := by simp [es1, hlen]
  have hbd1 : ∀ j < m, s₁.mem (eb1 + 4 * j) < n ∧ s₁.mem (eb1 + 4 * j + 1) < n := fun j hj => by
    have hj' : j < es1.length := hlen1.symm ▸ hj
    obtain ⟨hu, hv, _, _⟩ := hidx1 j hj'
    exact ⟨hu ▸ (es1[j]'hj').u.isLt, hv ▸ (es1[j]'hj').v.isLt⟩
  have h2 := framedTriple_iff_realization.mp
    (dedupSimpleEdgesProg_spec (es := es1) h16 hwf1 hidx1 (by rw [hlen1, heb1, hs1_fr])
      (by rw [hlen1, hs1_fr]; exact hfit.of_le (by omega)))
  simp only [hlen1] at h2
  obtain ⟨_, _, _, hdd_n, hdd_fr, hs2_fr, _, esOut, hesOut_len, hesOut_sub, hholds2, _⟩ := h2
  have hm_out : esOut.length ≤ m := hlen1 ▸ hesOut_sub.length_le
  refine ⟨⟨by omega, by rw [hs1_fr]; exact hfit.of_le (by omega), hbd1⟩,
    ⟨hdd_fr, by rw [hdd_n]; exact hfit.of_le (by omega), fun j hj => by
      have hj' : j < esOut.length := hesOut_len.symm ▸ hj
      obtain ⟨hu, hv, _, _⟩ := hholds2 j hj'
      rw [hdd_n]
      exact ⟨hu ▸ (esOut[j]'hj').u.isLt, hv ▸ (esOut[j]'hj').v.isLt⟩⟩⟩

/-- Uniform `Realizes .exact` certificate for `initPreprocessProg` with `work = 0`. -/
theorem realizes_initPreprocessProg : Realizes .exact
    initPreprocessProg WordEncoding.encode WordEncoding.encode
    initPreprocessProgSafe (fun _ _ => 0) := by
  unfold initPreprocessProg
  realize [realizes_initIndexedEdges, realizes_dedupSimpleEdgesProg, realizes_compactVerticesProg]
  all_goals
    obtain ⟨p1, p2⟩ := initPreprocess_word_post hmem h
    first
    | exact h.1 | exact h.2.1 | exact h.2.2.1.of_le (by omega)
    | exact p1.1 | exact p1.2.1 | exact p1.2.2
    | exact p2.1 | exact p2.2.1 | exact p2.2.2

/-- Framed `O(m + n)` specification for `initPreprocessProg`: indexes raw stride-3 edges,
deduplicates self-loops and parallel edges, and compacts isolated vertices, returning a simple
non-isolated `GraphSlice` `res` above `s.frontier` satisfying `res.numVertices ≤ 2 * res.numEdges`
and initial `MSFLiftInv es [] es₀`, in at most `63 * es.length + 9 * n + 9` memory operations
with `Modifies ∅`. -/
theorem initPreprocessProg_spec {w n inBase : ℕ} {es : List (WeightedEdge n ℕ)}
    {s : Memory.State} (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hraw : HoldsEdges inBase es s.mem) (hin : inBase + 3 * es.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + (21 * es.length + 3 * n + 1))) :
    Memory.FramedTriple w s (initPreprocessProg ⟨n, es.length, inBase⟩)
      (63 * es.length + 9 * n + 9) ∅ fun res s' =>
        res.numVertices ≤ 2 * res.numEdges ∧
        res.numVertices ≤ n ∧
        res.numEdges ≤ es.length ∧
        s.frontier ≤ res.edgeBase ∧
        res.edgeBase + 4 * res.numEdges ≤ s'.frontier ∧
        s'.frontier ≤ s.frontier + (21 * es.length + 3 * n + 1) ∧
        Memory.WellFormed w s' ∧
        ∃ es₀ : List (IndexedEdge res.numVertices),
          es₀.length = res.numEdges ∧
          HoldsIndexedEdges res.edgeBase es₀ s'.mem ∧
          IsSimple (edgeEnds (es₀.map IndexedEdge.toWeighted)) ∧
          (res.numEdges = 0 ↔ ∀ e ∈ es, e.u = e.v) ∧
          MSFLiftInv es [] es₀ := by
  dsimp only [initPreprocessProg]
  let es1 : List (IndexedEdge n) := es.mapIdx fun i e => ⟨e.u, e.v, e.weight, i⟩
  have hes1_len : es1.length = es.length := by simp [es1]
  have h1 := initIndexedEdges_spec (w := w) (n := n) (inBase := inBase) (es := es) (s := s)
    h16 hwf hraw hin (hfit.of_le (by omega))
  refine (Memory.FramedTriple.bind_same (c₂ := 55 * es.length + 9 * n + 8)
    (h1.mono le_rfl fun eb1 s₁ ⟨heb1, hs1_fr, hwf1, hholds1⟩ => ?_)).mono
    (by omega) fun _ _ h => h
  have h2 := dedupSimpleEdgesProg_spec (w := w) (n := n) (edgeBase := eb1) (es := es1) (s := s₁)
    h16 hwf1 hholds1 (by rw [hes1_len, heb1, hs1_fr])
    (by rw [hes1_len, hs1_fr]; exact hfit.of_le (by omega))
  simp only [hes1_len] at h2
  have h2m : Memory.FramedTriple w s₁ (dedupSimpleEdgesProg ⟨n, es.length, eb1⟩)
      (41 * es.length + 6 * n + 6) ∅ fun dd s₂ => Memory.Modifies ∅ s₁ s₂ ∧
        dd.numVertices = n ∧ dd.edgeBase + 4 * dd.numEdges ≤ s₂.frontier ∧
        s₂.frontier ≤ s₁.frontier + (13 * es.length + 2 * n) ∧ Memory.WellFormed w s₂ ∧
        ∃ esOut : List (IndexedEdge n), esOut.length = dd.numEdges ∧ esOut.Subperm es1 ∧
          HoldsIndexedEdges dd.edgeBase esOut s₂.mem ∧
          esOut.map IndexedEdge.toWeighted = dedupSimpleEdges (es1.map IndexedEdge.toWeighted) ∧
          IsSimple (edgeEnds (esOut.map IndexedEdge.toWeighted)) ∧
          ∀ e ∈ es1, e.u ≠ e.v → ∃ e' ∈ esOut, s(e'.u, e'.v) = s(e.u, e.v) ∧
            e'.weight ≤ e.weight :=
    Memory.Triple.mono h2 le_rfl fun _ _ ⟨hm, hq⟩ => ⟨hm, hm, hq⟩
  refine (Memory.FramedTriple.bind_same (c₂ := 14 * es.length + 3 * n + 2)
    (h2m.mono le_rfl fun dd s₂
      ⟨hmod₂, hdd_n, hdd_fr, hs2_fr, hwf2, esOut1, hesOut1_len, hesOut1_sub, hholds2, hdedup_eq,
        hsimp2, hdedup_rep⟩ => ?_)).mono (by omega) fun _ _ h => h
  have hm1_le : esOut1.length ≤ es.length := hes1_len ▸ hesOut1_sub.length_le
  have h3 := compactVerticesProg_spec (w := w) (n := n) (edgeBase := dd.edgeBase)
    (es := esOut1) (s := s₂) h16 hwf2 hholds2 (by rw [hesOut1_len]; exact hdd_fr)
    (hfit.of_le (by omega))
  have hdd_eq : (⟨n, esOut1.length, dd.edgeBase⟩ : GraphSlice) = dd := by
    cases dd
    simp only at hdd_n hesOut1_len
    rw [hdd_n, hesOut1_len]
  rw [hdd_eq] at h3
  refine (Memory.FramedTriple.bind_same (c₂ := 0) (h3.mono le_rfl fun cp s₃
    ⟨hcp_lift, hcp_eb, hcp_n, hs3_fr, hwf3, lift, es₀, hlift_inj, hes₀_len, hholds3, _, hnoiso,
      hlift_eq⟩ => ?_)).mono (by omega) fun _ _ h => h
  rw [← hesOut1_len]
  have hs1_le_s2 : s₁.frontier ≤ s₂.frontier := hmod₂.1
  refine Memory.FramedTriple.pure ⟨by
    rw [← hes₀_len]; exact card_le_two_mul_of_noIsolated hnoiso,
    hcp_n, hm1_le, by dsimp only; omega, by dsimp only; omega, by omega, hwf3, es₀, hes₀_len,
    hholds3,
    compactVertices_isSimple hlift_eq hsimp2, ?_, ?_⟩
  · constructor
    · intro h0 e he
      have hnil : esOut1 = [] := List.eq_nil_of_length_eq_zero h0
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
      have he1 : (⟨es[i].u, es[i].v, es[i].weight, i⟩ : IndexedEdge n) ∈ es1 :=
        List.mem_mapIdx.mpr ⟨i, hi, rfl⟩
      by_contra hne
      obtain ⟨e', he', _⟩ := hdedup_rep _ he1 hne
      rw [hnil] at he'
      simp at he'
    · intro hall
      cases h_out : esOut1 with
      | nil => rfl
      | cons eOut rest =>
        exfalso
        have hmem1 : eOut ∈ es1 :=
          hesOut1_sub.subset (by rw [h_out]; exact List.mem_cons_self)
        obtain ⟨i, hi, heq⟩ := List.mem_mapIdx.mp hmem1
        have hdiag : ¬ (edgeEnds (esOut1.map IndexedEdge.toWeighted)
            ⟨0, by rw [h_out]; simp⟩).IsDiag :=
          ((isSimple_iff _).mp hsimp2).1 ⟨0, by rw [h_out]; simp⟩
        have heq_uv : eOut.u = eOut.v := by
          have h := hall es[i] (List.getElem_mem hi)
          rw [← heq]
          exact h
        have hmk : edgeEnds (esOut1.map IndexedEdge.toWeighted) ⟨0, by rw [h_out]; simp⟩ =
            s(eOut.u, eOut.u) := by
          simp [h_out, edgeEnds, IndexedEdge.toWeighted, heq_uv]
        rw [hmk] at hdiag
        exact hdiag (by simp)
  · have hsp_range : (es₀.map IndexedEdge.id).Subperm (List.range es.length) := by
      have hid_map : es₀.map IndexedEdge.id = esOut1.map IndexedEdge.id := by
        rw [← hlift_eq, List.map_map]; rfl
      rw [hid_map, ← mapIdx_id_eq_range es]
      obtain ⟨l, hp, hs⟩ := List.subperm_iff.mp hesOut1_sub
      exact List.subperm_iff.mpr ⟨l.map IndexedEdge.id, hp.map _, hs.map _⟩
    have hnodup₀ : (es₀.map IndexedEdge.id).Nodup := by
      obtain ⟨l, hp, hs⟩ := List.subperm_iff.mp hsp_range
      exact (hp.nodup_iff.mpr List.nodup_range).sublist hs
    have hlt₀ : ∀ e ∈ es₀, e.id < es.length := fun e he =>
      List.mem_range.mp (hsp_range.subset (List.mem_map.mpr ⟨e, he, rfl⟩))
    refine ⟨List.nodup_nil, hnodup₀, hlt₀, fun _ h => by simp at h, fun L hL hmsf => ?_⟩
    have hL_lt : ∀ e ∈ L, e.id < es.length := fun e he => hlt₀ e (hL.subset he)
    let remIds : List (Fin es.length) := L.pmap (fun e he => ⟨e.id, hL_lt e he⟩) (fun _ he => he)
    have hrem_val : remIds.map Fin.val = L.map IndexedEdge.id := by
      apply List.ext_getElem <;> simp [remIds]
    let L_out : List (IndexedEdge n) := L.map fun e => ⟨lift e.u, lift e.v, e.weight, e.id⟩
    have hL_out_sub1 : L_out.Subperm esOut1 := by
      rw [← hlift_eq]
      obtain ⟨l, hp, hs⟩ := List.subperm_iff.mp hL
      exact List.subperm_iff.mpr ⟨l.map _, hp.map _, hs.map _⟩
    have hL_out_sub : L_out.Subperm es1 := hL_out_sub1.trans hesOut1_sub
    have hmsf_out1 : IsMinSpanningForest (esOut1.map IndexedEdge.toWeighted)
        (L_out.map IndexedEdge.toWeighted) := by
      have hm1 : L_out.map IndexedEdge.toWeighted =
          contractEdgeList lift (L.map IndexedEdge.toWeighted) := by
        simp [L_out, contractEdgeList, List.map_map, Function.comp, contractEdge,
          IndexedEdge.toWeighted]
      rw [hm1]
      exact compactVertices_isMinSpanningForest hlift_inj hlift_eq hmsf
    have hmsf_es1 : IsMinSpanningForest (es1.map IndexedEdge.toWeighted)
        (L_out.map IndexedEdge.toWeighted) :=
      isMinSpanningForest_of_dedupSimpleEdges _ _ (hdedup_eq ▸ hmsf_out1)
    rw [mapIdx_toWeighted es] at hmsf_es1
    have hL_out_eq : L_out.map IndexedEdge.toWeighted = remIds.map fun i => es[i.val] := by
      apply List.ext_getElem
      · simp [L_out, remIds]
      · intro i hi1 hi2
        have hi_out : i < L_out.length := by simpa using hi1
        have hmem_out : L_out[i] ∈ es1 := hL_out_sub.subset (List.getElem_mem hi_out)
        obtain ⟨_, heq_w⟩ := mem_mapIdx_eq hmem_out
        simp only [List.getElem_map, List.getElem_pmap, L_out, remIds] at heq_w ⊢
        exact heq_w
    rw [hL_out_eq] at hmsf_es1
    exact ⟨remIds, hrem_val, by simpa using hmsf_es1⟩

/-- Any safe Word-RAM state for `initPreprocessProg` outputs at most `a.numVertices` compacted
vertices. -/
theorem initPreprocessProg_numVertices_le {w : ℕ} {a : InitPreprocessArgs} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hsafe : initPreprocessProgSafe w a s) :
    ((Memory.spec 0).clientResult s (initPreprocessProg a)).numVertices ≤ a.numVertices := by
  rcases a with ⟨n, m, inBase⟩
  obtain ⟨rawEs, hlen, hraw⟩ := exists_rawEdges_of_initPreprocessSafe hsafe
  obtain ⟨h16, hin, hfit, _⟩ := hsafe
  dsimp only at hlen hraw hin hfit ⊢
  have h := framedTriple_iff_realization.mp (initPreprocessProg_spec h16 hwf hraw
    (by simpa [hlen] using hin) (by simpa [hlen] using hfit))
  simpa [hlen] using h.2.2.2.2.1

/-! ## Section 3: 3-Stage Borůvka Contraction Pipeline -/

/-- Input arguments for `boruvkaThreeStageProg`. -/
structure BoruvkaStageArgs where
  /-- Current vertex count `nCur`. -/
  numVertices : ℕ
  /-- Current edge count `mCur`. -/
  numEdges : ℕ
  /-- Base address of current stride-4 `IndexedEdge` array. -/
  edgeBase : ℕ
  /-- Base address of accumulated original MSF edge-ID array. -/
  selBase : ℕ
  /-- Current number of edge IDs already stored at `selBase`. -/
  selOff : ℕ
  deriving DecidableEq

/-- Faithful 5-word encoding of `BoruvkaStageArgs` as
`[numVertices, numEdges, edgeBase, selBase, selOff]`. -/
word_enc_structure encBoruvkaStageArgs : BoruvkaStageArgs where
  numVertices : wordWords,
  numEdges : wordWords,
  edgeBase : wordWords,
  selBase : wordWords,
  selOff : wordWords

instance : WordEncoding BoruvkaStageArgs := ⟨5, encBoruvkaStageArgs⟩

/-- Output state returned by a Borůvka contraction stage program. -/
structure BoruvkaStageResult where
  /-- Remaining active vertex count after contraction. -/
  numVertices : ℕ
  /-- Remaining edge count after contraction and deduplication. -/
  numEdges : ℕ
  /-- Base address of the compacted, deduplicated stride-4 output edges. -/
  edgeBase : ℕ
  /-- Updated number of accumulated original MSF edge IDs stored at `selBase`. -/
  selOff : ℕ
  deriving DecidableEq

/-- Faithful 4-word encoding of `BoruvkaStageResult` as
`[numVertices, numEdges, edgeBase, selOff]`. -/
word_enc_structure encBoruvkaStageResult : BoruvkaStageResult where
  numVertices : wordWords,
  numEdges : wordWords,
  edgeBase : wordWords,
  selOff : wordWords

instance : WordEncoding BoruvkaStageResult := ⟨4, encBoruvkaStageResult⟩

private def boruvkaStagePre (fBound : ℕ → ℕ → ℕ) (w : ℕ) (a : BoruvkaStageArgs)
    (s : Memory.State) : Prop :=
  Fits w 16 ∧
  a.edgeBase + 4 * a.numEdges ≤ s.frontier ∧
  a.selBase + a.selOff + a.numEdges ≤ s.frontier ∧
  Fits w (s.frontier + fBound a.numVertices a.numEdges) ∧
  ∀ j < a.numEdges,
    s.mem (a.edgeBase + 4 * j) < a.numVertices ∧
    s.mem (a.edgeBase + 4 * j + 1) < a.numVertices

private def boruvkaOneStageProg (a : BoruvkaStageArgs) : Memory.Prog BoruvkaStageResult := do
  let b ← boruvkaStepProg ⟨a.numVertices, a.numEdges, a.edgeBase⟩
  let sl ← appendSelIdsProg ⟨b.selBase, a.selBase, a.selOff, b.selCount⟩
  pure ⟨b.outVertices, b.outEdges, b.outBase, sl⟩

private def boruvkaOneStageProgSafe (w : ℕ) (a : BoruvkaStageArgs) (s : Memory.State) : Prop :=
  boruvkaStagePre (fun n m => 22 * m + 16 * n + 4) w a s

private theorem selCount_add_outEdges_le {n : ℕ} {selIdxs outIdxs : List (Fin n)}
    (hsel_nd : selIdxs.Nodup) (hout_nd : outIdxs.Nodup)
    (hdisj : ∀ i ∈ selIdxs, i ∉ outIdxs) :
    selIdxs.length + outIdxs.length ≤ n := by
  have hnd : (selIdxs ++ outIdxs).Nodup :=
    List.nodup_append.mpr ⟨hsel_nd, hout_nd, fun a ha b hb heq => hdisj a ha (heq ▸ hb)⟩
  have hsub : (selIdxs ++ outIdxs).Subperm (List.finRange n) :=
    List.subperm_of_subset hnd fun _ _ => List.mem_finRange _
  have hlen := hsub.length_le
  simp only [List.length_append, List.length_finRange] at hlen
  exact hlen

private theorem boruvkaOneStage_core_spec {w : ℕ} {a : BoruvkaStageArgs}
    {esCur : List (IndexedEdge a.numVertices)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hholds : HoldsIndexedEdges a.edgeBase esCur s.mem)
    (hlen : esCur.length = a.numEdges)
    (hedges_fr : a.edgeBase + 4 * a.numEdges ≤ s.frontier)
    (hsel_fr : a.selBase + a.selOff + a.numEdges ≤ s.frontier)
    (hfit : Fits w (s.frontier + (22 * a.numEdges + 16 * a.numVertices + 4))) :
    Memory.FramedTriple w s (boruvkaOneStageProg a)
      (78 * a.numEdges + 61 * a.numVertices + 34)
      (Set.Ico (a.selBase + a.selOff) (a.selBase + a.selOff + a.numEdges))
      fun res s' =>
        2 * res.numVertices ≤ a.numVertices ∧
        a.selOff ≤ res.selOff ∧
        res.selOff + res.numEdges ≤ a.selOff + a.numEdges ∧
        s.frontier ≤ res.edgeBase ∧
        res.edgeBase + 4 * res.numEdges ≤ s'.frontier ∧
        s'.frontier ≤ s.frontier + (22 * a.numEdges + 16 * a.numVertices + 4) ∧
        Memory.WellFormed w s' ∧
        ∃ (selIdxs : List (Fin esCur.length)) (esOut : List (IndexedEdge res.numVertices)),
          selIdxs.length = res.selOff - a.selOff ∧
          selIdxs.Nodup ∧
          esOut.length = res.numEdges ∧
          HoldsIndexedEdges res.edgeBase esOut s'.mem ∧
          IsSimple (edgeEnds (esOut.map IndexedEdge.toWeighted)) ∧
          (∀ j (hj : j < selIdxs.length),
            s'.mem (a.selBase + a.selOff + j) = (esCur[selIdxs[j].val]).id) ∧
          (∀ e ∈ esOut, ∃ i ∈ esCur, e.id = i.id) ∧
          ((esCur.map IndexedEdge.id).Nodup →
            (∀ i ∈ selIdxs, ∀ e ∈ esOut, e.id ≠ (esCur[i.val]).id) ∧
            (esOut.map IndexedEdge.id).Nodup) ∧
          (∀ L_out : List (IndexedEdge res.numVertices),
            L_out.Subperm esOut →
            IsMinSpanningForest (esOut.map IndexedEdge.toWeighted)
              (L_out.map IndexedEdge.toWeighted) →
            ∃ L_orig : List (IndexedEdge a.numVertices),
              (selIdxs.map (fun i => esCur[i.val]) ++ L_orig).Subperm esCur ∧
              L_orig.map IndexedEdge.id = L_out.map IndexedEdge.id ∧
              IsMinSpanningForest (esCur.map IndexedEdge.toWeighted)
                ((selIdxs.map (fun i => esCur[i.val]) ++ L_orig).map IndexedEdge.toWeighted)) := by
  dsimp only [boruvkaOneStageProg]
  let S : Set ℕ := Set.Ico (a.selBase + a.selOff) (a.selBase + a.selOff + a.numEdges)
  have hb := boruvkaStepProg_spec h16 hwf hholds (by rw [hlen]; exact hedges_fr)
    (by rw [hlen]; exact hfit)
  rw [show (⟨a.numVertices, esCur.length, a.edgeBase⟩ : GraphSlice) =
    ⟨a.numVertices, a.numEdges, a.edgeBase⟩ from by rw [hlen]] at hb
  simp only [hlen] at hb
  refine (Memory.FramedTriple.bind_same (c₂ := 2 * a.numEdges)
    ((hb.frame_mono (Set.empty_subset S)).mono le_rfl fun b s₁
      ⟨hs1_fr, hsel_ge, hsel_fr1, hout_ge, hout_fr1, hn_out, hm_out, _, hsel_le, hwf₁,
        selIdxs, outIdxs, esOut, hsel_len, hsel_nd, hout_len, hout_nd, hesOut_len, hdisj_io,
        hholds_sel, hholds_out, hsimp_out, _, hid_out, hmsf_lift, _, _⟩ => ?_)).mono
    (by omega) fun _ _ h => h
  have hsum_step : b.selCount + b.outEdges ≤ a.numEdges := by
    rw [← hsel_len, ← hout_len]
    exact hlen ▸ selCount_add_outEdges_le hsel_nd hout_nd hdisj_io
  let selSrcEs := selIdxs.map fun i => esCur[i.val]
  have hselSrc_len : selSrcEs.length = b.selCount := by simp [selSrcEs, hsel_len]
  have ha := appendSelIdsProg_spec (srcEs := selSrcEs) (dstBase := a.selBase) (dstOff := a.selOff)
    h16 hwf₁ hholds_sel (by rw [hselSrc_len]; exact hsel_fr1) (by rw [hselSrc_len]; omega)
    (Or.inr (by rw [hselSrc_len]; omega))
  have hS_sub : Set.Ico (a.selBase + a.selOff) (a.selBase + a.selOff + selSrcEs.length) ⊆ S :=
    fun x hx => by simp only [S, Set.mem_Ico] at hx ⊢; rw [hselSrc_len] at hx; omega
  have hdisj_out : Disjoint S (Set.Ico b.outBase (b.outBase + 4 * esOut.length)) :=
    Set.disjoint_left.mpr fun _ hx₁ hx₂ => by
      simp only [S, Set.mem_Ico] at hx₁ hx₂; omega
  have ha' := holdsIndexedEdges_frame_mem (ha.frame_mono hS_sub) hholds_out hdisj_out
    (by rw [hesOut_len]; exact hout_fr1)
  have hprog_eq : (⟨b.selBase, a.selBase, a.selOff, selSrcEs.length⟩ : AppendSelIdsArgs) =
      ⟨b.selBase, a.selBase, a.selOff, b.selCount⟩ := by
    rw [hselSrc_len]
  rw [hprog_eq] at ha'
  refine (Memory.FramedTriple.bind_same (c₂ := 0)
    (ha'.mono (by omega : 2 * selSrcEs.length ≤ 2 * a.numEdges) fun sl s₂
      ⟨⟨hsl_eq, hs2_fr, hwf₂, hwritten⟩, hholds_out2⟩ => ?_)).mono le_rfl fun _ _ h => h
  have hs2_le : s₂.frontier ≤ s.frontier + (22 * a.numEdges + 16 * a.numVertices + 4) := by
    omega
  refine Memory.FramedTriple.pure ⟨hn_out, by dsimp only; omega, by dsimp only; omega, hout_ge,
    by rw [hs2_fr]; exact hout_fr1, hs2_le, hwf₂, selIdxs, esOut, by dsimp only; omega, hsel_nd,
    hesOut_len, hholds_out2, hsimp_out, fun j hj => ?_, fun e he => ?_,
    fun hnd_id => ⟨?_, ?_⟩, hmsf_lift⟩
  · have hw := hwritten j (by simpa [selSrcEs] using hj)
    simpa [selSrcEs] using hw
  · have hm : e.id ∈ esOut.map IndexedEdge.id := List.mem_map.mpr ⟨e, he, rfl⟩
    rw [hid_out, List.mem_map] at hm
    obtain ⟨i, _, hi⟩ := hm
    exact ⟨esCur[i.val], List.getElem_mem _, hi.symm⟩
  · intro i hi e he hid
    have hm : e.id ∈ esOut.map IndexedEdge.id := List.mem_map.mpr ⟨e, he, rfl⟩
    rw [hid_out, List.mem_map] at hm
    obtain ⟨io, hio, hio_eq⟩ := hm
    have hget : (esCur.map IndexedEdge.id)[io.val]'(by simp [io.isLt]) =
        (esCur.map IndexedEdge.id)[i.val]'(by simp [i.isLt]) := by
      simp [hio_eq, hid]
    have hfin : io = i := Fin.ext (hnd_id.getElem_inj_iff.mp hget)
    subst hfin
    exact hdisj_io io hi hio
  · rw [hid_out]
    exact nodup_map_id_of_nodup hnd_id hout_nd

private theorem boruvkaOneStage_word_post {w : ℕ} {fBound : ℕ → ℕ → ℕ}
    {a : BoruvkaStageArgs} {s : Memory.State}
    (hf : 22 * a.numEdges + 16 * a.numVertices + 4 ≤ fBound a.numVertices a.numEdges)
    (hwf : Memory.WellFormed w s) (hsafe : boruvkaStagePre fBound w a s) :
    let g : GraphSlice := ⟨a.numVertices, a.numEdges, a.edgeBase⟩
    let b := (Memory.spec 0).clientResult s (boruvkaStepProg g)
    let s₁ := (Memory.spec 0).clientState s (boruvkaStepProg g)
    let res := (Memory.spec 0).clientResult s (boruvkaOneStageProg a)
    let s₂ := (Memory.spec 0).clientState s (boruvkaOneStageProg a)
    (Fits w 16 ∧ b.selBase + 4 * b.selCount ≤ s₁.frontier ∧
      a.selBase + a.selOff + b.selCount ≤ s₁.frontier) ∧
    (2 * res.numVertices ≤ a.numVertices ∧
      a.selOff ≤ res.selOff ∧
      res.selOff + res.numEdges ≤ a.selOff + a.numEdges ∧
      s.frontier ≤ res.edgeBase ∧
      res.edgeBase + 4 * res.numEdges ≤ s₂.frontier ∧
      s₂.frontier ≤ s.frontier + (22 * a.numEdges + 16 * a.numVertices + 4) ∧
      a.selBase + res.selOff + res.numEdges ≤ s₂.frontier ∧
      Memory.WellFormed w s₂ ∧
      ∀ j < res.numEdges, s₂.mem (res.edgeBase + 4 * j) < res.numVertices ∧
        s₂.mem (res.edgeBase + 4 * j + 1) < res.numVertices) := by
  obtain ⟨h16, hedges_fr, hsel_fr, hfit, hedges⟩ := hsafe
  obtain ⟨esCur, hlen, hholds⟩ := exists_indexedEdges_of_mem_lt hedges
  have hb := framedTriple_iff_realization.mp
    (boruvkaStepProg_spec h16 hwf hholds (by rw [hlen]; exact hedges_fr)
      (by rw [hlen]; exact hfit.of_le (Nat.add_le_add_left hf s.frontier)))
  rw [show (⟨a.numVertices, esCur.length, a.edgeBase⟩ : GraphSlice) =
    ⟨a.numVertices, a.numEdges, a.edgeBase⟩ from by rw [hlen]] at hb
  simp only [hlen] at hb
  obtain ⟨_, _, hmod₁, _, _, hsel_fr1, _, _, _, _, _, hsel_le, _, _⟩ := hb
  have hc := framedTriple_iff_realization.mp
    (boruvkaOneStage_core_spec h16 hwf hholds hlen hedges_fr hsel_fr
      (hfit.of_le (Nat.add_le_add_left hf s.frontier)))
  obtain ⟨_, _, hmod2, hn_out, hoff_le, hsum_out, hout_ge, hout_fr2, hs2_le, hwf₂, _, esOut,
    _, _, hesOut_len, hholds_out2, _⟩ := hc
  refine ⟨⟨h16, hsel_fr1, by have := hmod₁.1; omega⟩, hn_out, hoff_le, hsum_out, hout_ge,
    hout_fr2, hs2_le, by have := hmod2.1; omega, hwf₂, fun j hj => ?_⟩
  have hj' : j < esOut.length := hesOut_len.symm ▸ hj
  obtain ⟨hu, hv, _, _⟩ := hholds_out2 j hj'
  exact ⟨hu ▸ (esOut[j]'hj').u.isLt, hv ▸ (esOut[j]'hj').v.isLt⟩

private theorem realizes_boruvkaOneStageProg : Realizes .exact
    boruvkaOneStageProg WordEncoding.encode WordEncoding.encode
    boruvkaOneStageProgSafe (fun _ _ => 0) := by
  unfold boruvkaOneStageProg
  realize [realizes_boruvkaStepProg, realizes_appendSelIdsProg]
  all_goals
    obtain ⟨p1, _⟩ := boruvkaOneStage_word_post le_rfl hmem h
    try dsimp only [appendSelIdsProgSafe]
    first
    | exact h.1 | exact h.2.1 | exact h.2.2.2.1 | exact h.2.2.2.2
    | exact p1

private theorem boruvkaOneStageProg_spec {w n nCur edgeBase selBase : ℕ}
    {es : List (WeightedEdge n ℕ)} {accIds : List (Fin es.length)}
    {esCur : List (IndexedEdge nCur)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hholds : HoldsIndexedEdges edgeBase esCur s.mem)
    (hedges_fr : edgeBase + 4 * esCur.length ≤ s.frontier)
    (hacc_mem : ∀ j (hj : j < accIds.length), s.mem (selBase + j) = accIds[j].val)
    (hsel_fr : selBase + accIds.length + esCur.length ≤ s.frontier)
    (hinv : MSFLiftInv es accIds esCur)
    (hfit : Fits w (s.frontier + (22 * esCur.length + 16 * nCur + 4))) :
    Memory.FramedTriple w s
      (boruvkaOneStageProg ⟨nCur, esCur.length, edgeBase, selBase, accIds.length⟩)
      (78 * esCur.length + 61 * nCur + 34)
      (Set.Ico (selBase + accIds.length) (selBase + accIds.length + esCur.length))
      fun res s' =>
        2 * res.numVertices ≤ nCur ∧
        accIds.length ≤ res.selOff ∧
        res.selOff + res.numEdges ≤ accIds.length + esCur.length ∧
        s.frontier ≤ res.edgeBase ∧
        res.edgeBase + 4 * res.numEdges ≤ s'.frontier ∧
        s'.frontier ≤ s.frontier + (22 * esCur.length + 16 * nCur + 4) ∧
        Memory.WellFormed w s' ∧
        ∃ (accIds' : List (Fin es.length)) (es' : List (IndexedEdge res.numVertices)),
          es'.length = res.numEdges ∧
          HoldsIndexedEdges res.edgeBase es' s'.mem ∧
          IsSimple (edgeEnds (es'.map IndexedEdge.toWeighted)) ∧
          accIds'.length = res.selOff ∧
          (∀ j (hj : j < accIds'.length), s'.mem (selBase + j) = accIds'[j].val) ∧
          MSFLiftInv es accIds' es' := by
  let S : Set ℕ := Set.Ico (selBase + accIds.length) (selBase + accIds.length + esCur.length)
  have hcore := boruvkaOneStage_core_spec (w := w)
    (a := ⟨nCur, esCur.length, edgeBase, selBase, accIds.length⟩) h16 hwf hholds rfl
    hedges_fr hsel_fr hfit
  have hkept := hcore.frame_mem (D := Set.Ico selBase (selBase + accIds.length))
    (R := fun m => ∀ j (hj : j < accIds.length), m (selBase + j) = accIds[j].val)
    hacc_mem (fun m₁ m₂ heq hm j hj =>
      (heq (selBase + j) (Set.mem_Ico.mpr ⟨by omega, by omega⟩)).symm.trans (hm j hj))
    (Set.disjoint_left.mpr fun x hx₁ hx₂ => by simp only [Set.mem_Ico] at hx₁ hx₂; omega)
    (fun x hx => by simp only [Set.mem_Ico] at hx; omega)
  refine hkept.mono le_rfl fun res s'
    ⟨⟨hn_out, hoff_le, hsum_out, hout_ge, hout_fr, hs_le, hwf', selIdxs, esOut, hsel_len,
      hsel_nd, hesOut_len, hholds_out, hsimp_out, hwritten, hesOut_id, hdisj_nodup,
      hmsf_lift⟩, hacc_kept⟩ => ?_
  have ⟨hdisj_io, hesOut_nd⟩ := hdisj_nodup hinv.2.1
  have hsel_lt : ∀ i ∈ selIdxs, (esCur[i.val]).id < es.length := fun i _ =>
    hinv.2.2.1 _ (List.getElem_mem _)
  let newIds : List (Fin es.length) :=
    selIdxs.pmap (fun i hi => ⟨(esCur[i.val]).id, hsel_lt i hi⟩) (fun _ hi => hi)
  let accIds' : List (Fin es.length) := accIds ++ newIds
  have hnew_len : newIds.length = res.selOff - accIds.length := by simp [newIds, hsel_len]
  have hacc'_len : accIds'.length = res.selOff := by simp [accIds', hnew_len, hoff_le]
  have hacc'_mem : ∀ j (hj : j < accIds'.length), s'.mem (selBase + j) = accIds'[j].val := by
    intro j hj
    simp only [accIds', List.length_append] at hj
    by_cases hj1 : j < accIds.length
    · rw [List.getElem_append_left hj1]
      exact hacc_kept j hj1
    · have hj2 : j - accIds.length < newIds.length := by omega
      rw [List.getElem_append_right (by omega),
        show selBase + j = selBase + accIds.length + (j - accIds.length) by omega,
        hwritten (j - accIds.length) (by simpa [newIds] using hj2)]
      simp [newIds]
  have hnew_nd : newIds.Nodup := by
    apply List.Nodup.of_map Fin.val
    have hm : newIds.map Fin.val = selIdxs.map (fun i => (esCur[i.val]).id) := by
      apply List.ext_getElem <;> simp [newIds]
    rw [hm]
    exact nodup_map_id_of_nodup hinv.2.1 hsel_nd
  have hacc'_nd : accIds'.Nodup := by
    refine List.nodup_append.mpr ⟨hinv.1, hnew_nd, fun i hi j hj heq => ?_⟩
    subst heq
    obtain ⟨k, _, hk⟩ := List.mem_pmap.mp hj
    exact hinv.2.2.2.1 i hi esCur[k.val] (List.getElem_mem _) (congrArg Fin.val hk)
  have hesOut_lt : ∀ e ∈ esOut, e.id < es.length := fun e he => by
    obtain ⟨c, hc, hid⟩ := hesOut_id e he
    exact hid ▸ hinv.2.2.1 c hc
  have hesOut_disj : ∀ i ∈ accIds', ∀ e ∈ esOut, e.id ≠ i.val := by
    intro i hi e he hid
    rcases List.mem_append.mp hi with hi1 | hi2
    · obtain ⟨c, hc, hcid⟩ := hesOut_id e he
      exact hinv.2.2.2.1 i hi1 c hc (hcid ▸ hid)
    · obtain ⟨i_sel, his, his_eq⟩ := List.mem_pmap.mp hi2
      exact hdisj_io i_sel his e he (hid.trans (congrArg Fin.val his_eq).symm)
  have hinv' : MSFLiftInv es accIds' esOut := by
    refine ⟨hacc'_nd, hesOut_nd, hesOut_lt, hesOut_disj, fun L_out hL_sub hL_msf => ?_⟩
    obtain ⟨L_orig, hL_orig_sub, hL_orig_id, hL_orig_msf⟩ := hmsf_lift L_out hL_sub hL_msf
    obtain ⟨remIds, hrem_val, hrem_msf⟩ := hinv.2.2.2.2 _ hL_orig_sub hL_orig_msf
    have hsplit : remIds.map Fin.val = newIds.map Fin.val ++ L_orig.map IndexedEdge.id := by
      rw [hrem_val, List.map_append, List.map_map]
      congr 1
      apply List.ext_getElem <;> simp [newIds]
    have hlen_rem : newIds.length ≤ remIds.length := by
      have h := congrArg List.length hsplit
      simp only [List.length_map, List.length_append] at h
      omega
    let r1 := remIds.take newIds.length
    let r2 := remIds.drop newIds.length
    have hr1_eq : r1 = newIds := by
      apply List.ext_getElem
      · simp [r1, hlen_rem]
      · intro j hj1 hj2
        apply Fin.ext
        have htake_eq : r1.map Fin.val = newIds.map Fin.val := by
          have h := congrArg (List.take newIds.length) hsplit
          simpa [r1, List.map_take, List.take_left' (by simp : (newIds.map Fin.val).length ≤ _)]
            using h
        have hjv := congrArg (fun l => l[j]?) htake_eq
        simp only [List.getElem?_eq_getElem
            (by simp only [List.length_map]; simpa [r1] using hj1 : j < (r1.map Fin.val).length),
          List.getElem?_eq_getElem
            (by simp only [List.length_map]; exact hj2 : j < (newIds.map Fin.val).length),
          Option.some.injEq] at hjv
        simpa [List.getElem_map] using hjv
    have hr2_val : r2.map Fin.val = L_out.map IndexedEdge.id := by
      rw [← hL_orig_id]
      have hdrop := congrArg (List.drop newIds.length) hsplit
      simpa [r2, List.map_drop, List.drop_left' (by simp : (newIds.map Fin.val).length ≤ _)]
        using hdrop
    have hmerge : accIds ++ remIds = accIds' ++ r2 := by
      calc
        accIds ++ remIds = accIds ++ (r1 ++ r2) := by rw [List.take_append_drop]
        _ = accIds' ++ r2 := by rw [hr1_eq, List.append_assoc]
    rw [hmerge] at hrem_msf
    exact ⟨r2, hr2_val, hrem_msf⟩
  exact ⟨hn_out, hoff_le, hsum_out, hout_ge, hout_fr, hs_le, hwf', accIds', esOut, hesOut_len,
    hholds_out, hsimp_out, hacc'_len, hacc'_mem, hinv'⟩

private theorem boruvkaStage_seq_spec
    {w n nCur edgeBase selBase mulA costA frontA costOut frontOut : ℕ}
    {es : List (WeightedEdge n ℕ)} {accIds : List (Fin es.length)}
    {esCur : List (IndexedEdge nCur)} {s : Memory.State}
    {progA : BoruvkaStageArgs → Memory.Prog BoruvkaStageResult}
    (h16 : Fits w 16) (_hwf : Memory.WellFormed w s)
    (hsel_fr : selBase + accIds.length + esCur.length ≤ s.frontier)
    (hA : Memory.FramedTriple w s
      (progA ⟨nCur, esCur.length, edgeBase, selBase, accIds.length⟩) costA
      (Set.Ico (selBase + accIds.length) (selBase + accIds.length + esCur.length))
      fun res s' =>
        mulA * res.numVertices ≤ nCur ∧
        accIds.length ≤ res.selOff ∧
        res.selOff + res.numEdges ≤ accIds.length + esCur.length ∧
        s.frontier ≤ res.edgeBase ∧
        res.edgeBase + 4 * res.numEdges ≤ s'.frontier ∧
        s'.frontier ≤ s.frontier + frontA ∧
        Memory.WellFormed w s' ∧
        ∃ (accIds' : List (Fin es.length)) (es' : List (IndexedEdge res.numVertices)),
          es'.length = res.numEdges ∧
          HoldsIndexedEdges res.edgeBase es' s'.mem ∧
          IsSimple (edgeEnds (es'.map IndexedEdge.toWeighted)) ∧
          accIds'.length = res.selOff ∧
          (∀ j (hj : j < accIds'.length), s'.mem (selBase + j) = accIds'[j].val) ∧
          MSFLiftInv es accIds' es')
    (hmul_pos : 0 < mulA)
    (hcost : costA + (78 * esCur.length + 61 * (nCur / mulA) + 34) ≤ costOut)
    (hfront : frontA + (22 * esCur.length + 16 * (nCur / mulA) + 4) ≤ frontOut)
    (hfit2 : ∀ r1 : BoruvkaStageResult, mulA * r1.numVertices ≤ nCur →
      accIds.length ≤ r1.selOff →
      r1.selOff + r1.numEdges ≤ accIds.length + esCur.length →
      Fits w (s.frontier + frontA + (22 * r1.numEdges + 16 * r1.numVertices + 4))) :
    let S := Set.Ico (selBase + accIds.length) (selBase + accIds.length + esCur.length)
    Memory.FramedTriple w s
      (progA ⟨nCur, esCur.length, edgeBase, selBase, accIds.length⟩ >>= fun r1 =>
        boruvkaOneStageProg ⟨r1.numVertices, r1.numEdges, r1.edgeBase, selBase, r1.selOff⟩)
      costOut S
      fun res s' =>
        2 * mulA * res.numVertices ≤ nCur ∧
        accIds.length ≤ res.selOff ∧
        res.selOff + res.numEdges ≤ accIds.length + esCur.length ∧
        s.frontier ≤ res.edgeBase ∧
        res.edgeBase + 4 * res.numEdges ≤ s'.frontier ∧
        s'.frontier ≤ s.frontier + frontOut ∧
        Memory.WellFormed w s' ∧
        ∃ (accIds' : List (Fin es.length)) (es' : List (IndexedEdge res.numVertices)),
          es'.length = res.numEdges ∧
          HoldsIndexedEdges res.edgeBase es' s'.mem ∧
          IsSimple (edgeEnds (es'.map IndexedEdge.toWeighted)) ∧
          accIds'.length = res.selOff ∧
          (∀ j (hj : j < accIds'.length), s'.mem (selBase + j) = accIds'[j].val) ∧
          MSFLiftInv es accIds' es' := by
  let S := Set.Ico (selBase + accIds.length) (selBase + accIds.length + esCur.length)
  refine (Memory.FramedTriple.bind_same (c₂ := 78 * esCur.length + 61 * (nCur / mulA) + 34)
    (hA.mono le_rfl fun r1 s₁ ⟨hmul1, hoff1, hsum1, hed1_ge, hed1_fr, hs1_le, hwf1, acc1, es1,
      hes1_len, hholds1, hsimp1, hacc1_len, hacc1_mem, hinv1⟩ => ?_)).mono hcost
    fun _ _ h => h
  have hs1_ge : s.frontier ≤ s₁.frontier := by omega
  have hS1_sub : Set.Ico (selBase + acc1.length) (selBase + acc1.length + es1.length) ⊆ S :=
    fun x hx => by simp only [S, Set.mem_Ico] at hx ⊢; omega
  have hfit_r1 : Fits w (s₁.frontier + (22 * es1.length + 16 * r1.numVertices + 4)) :=
    (hfit2 r1 hmul1 hoff1 hsum1).of_le (by rw [hes1_len]; omega)
  have hB := boruvkaOneStageProg_spec h16 hwf1 hholds1 (by rw [hes1_len]; exact hed1_fr)
    hacc1_mem (by rw [hes1_len, hacc1_len]; omega) hinv1 hfit_r1
  rw [show (⟨r1.numVertices, es1.length, r1.edgeBase, selBase, acc1.length⟩ : BoruvkaStageArgs) =
    ⟨r1.numVertices, r1.numEdges, r1.edgeBase, selBase, r1.selOff⟩ from by
      rw [hes1_len, hacc1_len]] at hB
  have hmul_div : r1.numVertices ≤ nCur / mulA :=
    (Nat.le_div_iff_mul_le hmul_pos).mpr (by rw [Nat.mul_comm]; exact hmul1)
  exact (hB.frame_mono hS1_sub).mono (by rw [hes1_len]; omega) fun res s₂
    ⟨hn2, hoff2, hsum2, hed2_ge, hed2_fr, hs2_le, hwf2, acc2, es2, hes2_len, hholds2, hsimp2,
      hacc2_len, hacc2_mem, hinv2⟩ =>
    ⟨by rw [show 2 * mulA * res.numVertices = mulA * (2 * res.numVertices) by ring]
        exact le_trans (Nat.mul_le_mul_left mulA hn2) hmul1,
      by omega, by omega, hs1_ge.trans hed2_ge, hed2_fr,
      by rw [hes1_len] at hs2_le; omega, hwf2, acc2, es2, hes2_len, hholds2, hsimp2, hacc2_len,
      hacc2_mem, hinv2⟩

private def boruvkaTwoStageProg (a : BoruvkaStageArgs) : Memory.Prog BoruvkaStageResult := do
  let r1 ← boruvkaOneStageProg a
  boruvkaOneStageProg ⟨r1.numVertices, r1.numEdges, r1.edgeBase, a.selBase, r1.selOff⟩

private def boruvkaTwoStageProgSafe (w : ℕ) (a : BoruvkaStageArgs) (s : Memory.State) : Prop :=
  boruvkaStagePre (fun n m => 44 * m + 24 * n + 8) w a s

private theorem boruvkaTwoStage_word_post {w : ℕ} {fBound : ℕ → ℕ → ℕ}
    {a : BoruvkaStageArgs} {s : Memory.State}
    (hf : 44 * a.numEdges + 24 * a.numVertices + 8 ≤ fBound a.numVertices a.numEdges)
    (hwf : Memory.WellFormed w s) (hsafe : boruvkaStagePre fBound w a s) :
    let r1 := (Memory.spec 0).clientResult s (boruvkaOneStageProg a)
    let s₁ := (Memory.spec 0).clientState s (boruvkaOneStageProg a)
    boruvkaOneStageProgSafe w ⟨r1.numVertices, r1.numEdges, r1.edgeBase, a.selBase, r1.selOff⟩ s₁ ∧
    (let r2 := (Memory.spec 0).clientResult s (boruvkaTwoStageProg a)
     let s₂ := (Memory.spec 0).clientState s (boruvkaTwoStageProg a)
     4 * r2.numVertices ≤ a.numVertices ∧
     a.selOff ≤ r2.selOff ∧
     r2.selOff + r2.numEdges ≤ a.selOff + a.numEdges ∧
     s.frontier ≤ r2.edgeBase ∧
     r2.edgeBase + 4 * r2.numEdges ≤ s₂.frontier ∧
     s₂.frontier ≤ s.frontier + (44 * a.numEdges + 24 * a.numVertices + 8) ∧
     a.selBase + r2.selOff + r2.numEdges ≤ s₂.frontier ∧
     Memory.WellFormed w s₂ ∧
     ∀ j < r2.numEdges, s₂.mem (r2.edgeBase + 4 * j) < r2.numVertices ∧
       s₂.mem (r2.edgeBase + 4 * j + 1) < r2.numVertices) := by
  have ⟨_, p1⟩ := boruvkaOneStage_word_post (by omega : 22 * a.numEdges + 16 * a.numVertices + 4 ≤
    fBound a.numVertices a.numEdges) hwf hsafe
  obtain ⟨hn1, hoff1, hsum1, hed1_ge, hed1_fr, hs1_le, hsel1_fr, hwf1, hedges1⟩ := p1
  obtain ⟨h16, _, _, hfit, _⟩ := hsafe
  set r1 := (Memory.spec 0).clientResult s (boruvkaOneStageProg a)
  set s₁ := (Memory.spec 0).clientState s (boruvkaOneStageProg a)
  let a1 : BoruvkaStageArgs := ⟨r1.numVertices, r1.numEdges, r1.edgeBase, a.selBase, r1.selOff⟩
  have hsafe1 : boruvkaOneStageProgSafe w a1 s₁ :=
    ⟨h16, hed1_fr, hsel1_fr, hfit.of_le (by dsimp only [a1]; omega), hedges1⟩
  have ⟨_, p2⟩ := boruvkaOneStage_word_post le_rfl hwf1 hsafe1
  obtain ⟨hn2, hoff2, hsum2, hed2_ge, hed2_fr, hs2_le, hsel2_fr, hwf2, hedges2⟩ := p2
  have hres_eq : (Memory.spec 0).clientResult s (boruvkaTwoStageProg a) =
      (Memory.spec 0).clientResult s₁ (boruvkaOneStageProg a1) := by
    unfold boruvkaTwoStageProg
    rw [StateTransitionSpec.clientResult_bind]
  have hst_eq : (Memory.spec 0).clientState s (boruvkaTwoStageProg a) =
      (Memory.spec 0).clientState s₁ (boruvkaOneStageProg a1) := by
    unfold boruvkaTwoStageProg
    rw [StateTransitionSpec.clientState_bind]
  refine ⟨hsafe1, ?_⟩
  rw [hres_eq, hst_eq]
  dsimp only [a1] at *
  exact ⟨by omega, by omega, by omega, by omega, hed2_fr, by omega, hsel2_fr, hwf2, hedges2⟩

private theorem boruvkaStagePre_mono {f₁ f₂ : ℕ → ℕ → ℕ} {w : ℕ} {a : BoruvkaStageArgs}
    {s : Memory.State} (hle : f₁ a.numVertices a.numEdges ≤ f₂ a.numVertices a.numEdges)
    (h : boruvkaStagePre f₂ w a s) : boruvkaStagePre f₁ w a s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1.of_le (Nat.add_le_add_left hle s.frontier), h.2.2.2.2⟩

private theorem realizes_boruvkaTwoStageProg : Realizes .exact
    boruvkaTwoStageProg WordEncoding.encode WordEncoding.encode
    boruvkaTwoStageProgSafe (fun _ _ => 0) := by
  unfold boruvkaTwoStageProg
  realize [realizes_boruvkaOneStageProg]
  all_goals
    have ⟨hsafe2, _⟩ := boruvkaTwoStage_word_post le_rfl hmem h
    first
    | exact boruvkaStagePre_mono (by omega) h
    | exact hsafe2

private theorem boruvkaTwoStageProg_spec {w n nCur edgeBase selBase : ℕ}
    {es : List (WeightedEdge n ℕ)} {accIds : List (Fin es.length)}
    {esCur : List (IndexedEdge nCur)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hholds : HoldsIndexedEdges edgeBase esCur s.mem)
    (hedges_fr : edgeBase + 4 * esCur.length ≤ s.frontier)
    (hacc_mem : ∀ j (hj : j < accIds.length), s.mem (selBase + j) = accIds[j].val)
    (hsel_fr : selBase + accIds.length + esCur.length ≤ s.frontier)
    (hinv : MSFLiftInv es accIds esCur)
    (hfit : Fits w (s.frontier + (44 * esCur.length + 24 * nCur + 8))) :
    Memory.FramedTriple w s
      (boruvkaTwoStageProg ⟨nCur, esCur.length, edgeBase, selBase, accIds.length⟩)
      (156 * esCur.length + 92 * nCur + 68)
      (Set.Ico (selBase + accIds.length) (selBase + accIds.length + esCur.length))
      fun res s' =>
        4 * res.numVertices ≤ nCur ∧
        accIds.length ≤ res.selOff ∧
        res.selOff + res.numEdges ≤ accIds.length + esCur.length ∧
        s.frontier ≤ res.edgeBase ∧
        res.edgeBase + 4 * res.numEdges ≤ s'.frontier ∧
        s'.frontier ≤ s.frontier + (44 * esCur.length + 24 * nCur + 8) ∧
        Memory.WellFormed w s' ∧
        ∃ (accIds' : List (Fin es.length)) (es' : List (IndexedEdge res.numVertices)),
          es'.length = res.numEdges ∧
          HoldsIndexedEdges res.edgeBase es' s'.mem ∧
          IsSimple (edgeEnds (es'.map IndexedEdge.toWeighted)) ∧
          accIds'.length = res.selOff ∧
          (∀ j (hj : j < accIds'.length), s'.mem (selBase + j) = accIds'[j].val) ∧
          MSFLiftInv es accIds' es' := by
  exact boruvkaStage_seq_spec h16 hwf hsel_fr
    (boruvkaOneStageProg_spec h16 hwf hholds hedges_fr hacc_mem hsel_fr hinv
      (hfit.of_le (by omega)))
    (by omega) (by omega) (by omega) fun r1 hn1 hoff1 hsum1 => hfit.of_le (by omega)

/-- Execute three consecutive Borůvka contraction stages, appending selected original edge IDs
to `a.selBase` starting at `a.selOff`. -/
def boruvkaThreeStageProg (a : BoruvkaStageArgs) : Memory.Prog BoruvkaStageResult := do
  let r2 ← boruvkaTwoStageProg a
  boruvkaOneStageProg ⟨r2.numVertices, r2.numEdges, r2.edgeBase, a.selBase, r2.selOff⟩

/-- Closed-form Word-RAM safety domain for `boruvkaThreeStageProg`. -/
@[expose] def boruvkaThreeStageProgSafe (w : ℕ) (a : BoruvkaStageArgs)
    (s : Memory.State) : Prop :=
  Fits w 16 ∧
  a.edgeBase + 4 * a.numEdges ≤ s.frontier ∧
  a.selBase + a.selOff + a.numEdges ≤ s.frontier ∧
  Fits w (s.frontier + (66 * a.numEdges + 28 * a.numVertices + 12)) ∧
  ∀ j < a.numEdges,
    s.mem (a.edgeBase + 4 * j) < a.numVertices ∧
    s.mem (a.edgeBase + 4 * j + 1) < a.numVertices

/-- Uniform `Realizes .exact` certificate for `boruvkaThreeStageProg` with `work = 0`. -/
theorem realizes_boruvkaThreeStageProg : Realizes .exact
    boruvkaThreeStageProg WordEncoding.encode WordEncoding.encode
    boruvkaThreeStageProgSafe (fun _ _ => 0) := by
  unfold boruvkaThreeStageProg
  realize [realizes_boruvkaTwoStageProg, realizes_boruvkaOneStageProg]
  all_goals
    have h' : boruvkaStagePre (fun n m => 66 * m + 28 * n + 12) w d s := h
    have ⟨_, p2⟩ := boruvkaTwoStage_word_post
      (by omega : 44 * d.numEdges + 24 * d.numVertices + 8 ≤
        66 * d.numEdges + 28 * d.numVertices + 12)
      hmem h'
    obtain ⟨hn2, hoff2, hsum2, hed2_ge, hed2_fr, hs2_le, hsel2_fr, _, hedges2⟩ := p2
    have hfit : Fits w (s.frontier + (66 * d.numEdges + 28 * d.numVertices + 12)) := h.2.2.2.1
    first
    | exact boruvkaStagePre_mono (by omega) h'
    | (dsimp only [boruvkaOneStageProgSafe, boruvkaStagePre]
       exact ⟨h.1, hed2_fr, hsel2_fr, hfit.of_le (by omega), hedges2⟩)

/-- Framed `O(m + n)` specification for `boruvkaThreeStageProg`: runs three Borůvka contraction
stages, reducing active vertices by at least a factor of `8` (`8 * res.numVertices ≤ nCur`),
appending selected original edge IDs onto `selBase + accIds.length`, preserving `MSFLiftInv`, and
modifying only `Set.Ico (selBase + accIds.length) (selBase + accIds.length + esCur.length)`, in at
most `234 * esCur.length + 108 * nCur + 102` memory operations. -/
theorem boruvkaThreeStageProg_spec {w n nCur edgeBase selBase : ℕ}
    {es : List (WeightedEdge n ℕ)} {accIds : List (Fin es.length)}
    {esCur : List (IndexedEdge nCur)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hholds : HoldsIndexedEdges edgeBase esCur s.mem)
    (hedges_fr : edgeBase + 4 * esCur.length ≤ s.frontier)
    (hacc_mem : ∀ j (hj : j < accIds.length), s.mem (selBase + j) = accIds[j].val)
    (hsel_fr : selBase + accIds.length + esCur.length ≤ s.frontier)
    (hinv : MSFLiftInv es accIds esCur)
    (hfit : Fits w (s.frontier + (66 * esCur.length + 28 * nCur + 12))) :
    Memory.FramedTriple w s
      (boruvkaThreeStageProg ⟨nCur, esCur.length, edgeBase, selBase, accIds.length⟩)
      (234 * esCur.length + 108 * nCur + 102)
      (Set.Ico (selBase + accIds.length) (selBase + accIds.length + esCur.length))
      fun res s' =>
        8 * res.numVertices ≤ nCur ∧
        accIds.length ≤ res.selOff ∧
        res.selOff + res.numEdges ≤ accIds.length + esCur.length ∧
        s.frontier ≤ res.edgeBase ∧
        res.edgeBase + 4 * res.numEdges ≤ s'.frontier ∧
        s'.frontier ≤ s.frontier + (66 * esCur.length + 28 * nCur + 12) ∧
        Memory.WellFormed w s' ∧
        ∃ (accIds' : List (Fin es.length)) (es' : List (IndexedEdge res.numVertices)),
          es'.length = res.numEdges ∧
          HoldsIndexedEdges res.edgeBase es' s'.mem ∧
          IsSimple (edgeEnds (es'.map IndexedEdge.toWeighted)) ∧
          accIds'.length = res.selOff ∧
          (∀ j (hj : j < accIds'.length), s'.mem (selBase + j) = accIds'[j].val) ∧
          MSFLiftInv es accIds' es' := by
  exact boruvkaStage_seq_spec h16 hwf hsel_fr
    (boruvkaTwoStageProg_spec h16 hwf hholds hedges_fr hacc_mem hsel_fr hinv
      (hfit.of_le (by omega)))
    (by omega) (by omega) (by omega) fun r2 hn2 hoff2 hsum2 => hfit.of_le (by omega)

end Cslib.Algorithms.WordRAM.MinimumSpanningForest
