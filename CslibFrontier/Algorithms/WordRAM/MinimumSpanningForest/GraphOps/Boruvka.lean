/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.Dedup
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.Components
import CslibFrontier.Computability.WordRAM.Realization.LoopFrame
import CslibFrontier.Computability.WordRAM.Realization.RecordOps
import CslibFrontier.Foundations.Data.List.Subperm
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.ValidProg

/-!
# Linear-Time Borůvka Contraction Step

Implements one linear-time Borůvka contraction step ([PettieRamachandran2002], Section 2.1,
p. 18; toward Theorem 5.8, #8624) on `Cslib.DataStructure.Memory.Prog` over stride-4
`IndexedEdge` multigraphs (admitting disconnected graphs, self-loops, parallel edges, and
duplicate `ℕ` weights). Whereas [PettieRamachandran2002] assumes distinct edge weights and
groups two rounds as `Boruvka2`, this module implements a single contraction round with tied
weights broken deterministically by smallest list index, reducing the remaining vertex count to at
most half of the total input vertices after dropping isolated output vertices
(`2 * res.outVertices ≤ n`) in `O(m + n)` memory operations with `work = 0` and preserving MSF
liftability.

## Main definitions

* `BoruvkaSelectArgs`, `BoruvkaSelectResult`: argument/result encodings for `boruvkaSelectProg`.
* `BoruvkaPartitionResult`, `BoruvkaShrinkArgs`, `BoruvkaStepResult`: argument/result encodings for
  the partition, shrink, and combined Borůvka step programs.
* `IsVertexMinEdge`: characterizes a vertex's lightest incident non-loop edge under index
  tie-breaking.
* `boruvkaMinProg`: finds each vertex's lightest incident non-loop edge index (tie-broken by
  smallest index) in `O(m + n)` time with `work = 0`.
* `boruvkaSelectProg`: deduplicates and materializes selected Borůvka edges in `O(m + n)` time
  with `work = 0`.
* `boruvkaPartitionProg`: runs `boruvkaMinProg`, `boruvkaSelectProg`, and
  `connectedComponentsProg` in `O(m + n)` time.
* `boruvkaShrinkProg`: runs `contractEdgesProg`, `dedupSimpleEdgesProg`, and `compactVerticesProg`
  in `O(m + nComp)` time.
* `boruvkaStepProg`: runs one full Borůvka contraction round in `O(m + n)` time.

## Main results

* `realizes_boruvkaMinProg`, `boruvkaMinProg_spec`: WordRAM realization and framed `O(m + n)`
  specification for `boruvkaMinProg`.
* `realizes_boruvkaSelectProg`, `boruvkaSelectProg_spec`: WordRAM realization and framed
  `O(m + n)` specification for `boruvkaSelectProg`.
* `realizes_boruvkaPartitionProg`, `boruvkaPartitionProg_spec`: WordRAM realization and framed
  `O(m + n)` specification for `boruvkaPartitionProg`.
* `realizes_boruvkaShrinkProg`, `boruvkaShrinkProg_spec`: WordRAM realization and framed
  `O(m + nComp)` specification for `boruvkaShrinkProg`.
* `realizes_boruvkaStepProg`, `boruvkaStepProg_spec`: WordRAM realization and framed `O(m + n)`
  specification for `boruvkaStepProg`, reducing the remaining non-isolated output vertex count to
  at most half of the total input vertices (`2 * res.outVertices ≤ n`) and preserving minimum
  spanning forest liftability.
* `boruvkaStepProg_lift_msf`: pure lifting theorem recovering an MSF of the original graph from an
  MSF of the compacted contracted output.

## References

* [PettieRamachandran2002] Seth Pettie and Vijaya Ramachandran, *An Optimal Minimum Spanning Tree
  Algorithm*, Journal of the ACM 49(1), 16–34, 2002.
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Algorithms.WordRAM.Kruskal
open Cslib.Query.MinimumSpanningForest

/-! ## Public Argument and Result Encodings -/

/-- Arguments for `boruvkaSelectProg`: graph slice `(numVertices, numEdges, edgeBase)` together
with the vertex-minimum index array `minIdxBase`. -/
structure BoruvkaSelectArgs where
  /-- Number of vertices `n`. -/
  numVertices : ℕ
  /-- Number of edges `m`. -/
  numEdges : ℕ
  /-- Base address of the stride-4 `IndexedEdge` array. -/
  edgeBase : ℕ
  /-- Base address of the length-`n` array storing each vertex's minimum incident edge index. -/
  minIdxBase : ℕ

/-- Faithful four-word encoding of `BoruvkaSelectArgs` as
`[numVertices, numEdges, edgeBase, minIdxBase]`. -/
word_enc_structure encBoruvkaSelectArgs : BoruvkaSelectArgs where
  numVertices : wordWords,
  numEdges : wordWords,
  edgeBase : wordWords,
  minIdxBase : wordWords

instance : WordEncoding BoruvkaSelectArgs := ⟨4, encBoruvkaSelectArgs⟩

/-- Output handles produced by `boruvkaSelectProg`: base address and count of selected edges. -/
structure BoruvkaSelectResult where
  /-- Base address of the stride-4 selected `IndexedEdge` array. -/
  selBase : ℕ
  /-- Number of distinct selected Borůvka edges (`selCount ≤ n`, `selCount ≤ m`). -/
  selCount : ℕ

/-- Faithful two-word encoding of `BoruvkaSelectResult` as `[selBase, selCount]`. -/
word_enc_structure encBoruvkaSelectResult : BoruvkaSelectResult where
  selBase : wordWords,
  selCount : wordWords

instance : WordEncoding BoruvkaSelectResult := ⟨2, encBoruvkaSelectResult⟩

/-- Output handles produced by `boruvkaPartitionProg`: selected edges plus component labels. -/
structure BoruvkaPartitionResult where
  /-- Base address of the stride-4 selected `IndexedEdge` array. -/
  selBase : ℕ
  /-- Number of selected Borůvka edges. -/
  selCount : ℕ
  /-- Base address of the length-`n` component label array. -/
  compBase : ℕ
  /-- Number of connected components induced by the selected edges. -/
  numComps : ℕ

/-- Faithful four-word encoding of `BoruvkaPartitionResult` as
`[selBase, selCount, compBase, numComps]`. -/
word_enc_structure encBoruvkaPartitionResult : BoruvkaPartitionResult where
  selBase : wordWords,
  selCount : wordWords,
  compBase : wordWords,
  numComps : wordWords

instance : WordEncoding BoruvkaPartitionResult := ⟨4, encBoruvkaPartitionResult⟩

/-- Arguments for `boruvkaShrinkProg`: input graph slice `(numVertices, numEdges, edgeBase)`,
number of components `numComps`, and component label array `compBase`. -/
structure BoruvkaShrinkArgs where
  /-- Number of input vertices `n`. -/
  numVertices : ℕ
  /-- Number of contracted components `nComp`. -/
  numComps : ℕ
  /-- Number of input edges `m`. -/
  numEdges : ℕ
  /-- Base address of the input stride-4 `IndexedEdge` array. -/
  edgeBase : ℕ
  /-- Base address of the length-`n` component label array. -/
  compBase : ℕ

/-- Faithful five-word encoding of `BoruvkaShrinkArgs` as
`[numVertices, numComps, numEdges, edgeBase, compBase]`. -/
word_enc_structure encBoruvkaShrinkArgs : BoruvkaShrinkArgs where
  numVertices : wordWords,
  numComps : wordWords,
  numEdges : wordWords,
  edgeBase : wordWords,
  compBase : wordWords

instance : WordEncoding BoruvkaShrinkArgs := ⟨5, encBoruvkaShrinkArgs⟩

/-- Output handles produced by `boruvkaStepProg`: selected Borůvka edges and shrunk graph slice. -/
structure BoruvkaStepResult where
  /-- Base address of the selected stride-4 `IndexedEdge` array. -/
  selBase : ℕ
  /-- Number of selected Borůvka edges. -/
  selCount : ℕ
  /-- Non-isolated output vertices kept (`2 * outVertices ≤ n` total input vertices). -/
  outVertices : ℕ
  /-- Number of output edges (`outEdges ≤ m`). -/
  outEdges : ℕ
  /-- Base address of the compacted, deduplicated stride-4 output edges. -/
  outBase : ℕ

/-- Faithful five-word encoding of `BoruvkaStepResult` as
`[selBase, selCount, outVertices, outEdges, outBase]`. -/
word_enc_structure encBoruvkaStepResult : BoruvkaStepResult where
  selBase : wordWords,
  selCount : wordWords,
  outVertices : wordWords,
  outEdges : wordWords,
  outBase : wordWords

instance : WordEncoding BoruvkaStepResult := ⟨5, encBoruvkaStepResult⟩

/-- `idx` is the lightest non-loop edge in `es` incident to `x`, breaking equal-weight ties by
smallest list index. -/
@[expose] def IsVertexMinEdge {n : ℕ} (es : List (IndexedEdge n)) (x : Fin n)
    (idx : Fin es.length) : Prop :=
  (es[idx.val]).u ≠ (es[idx.val]).v ∧ ((es[idx.val]).u = x ∨ (es[idx.val]).v = x) ∧
  ∀ j : Fin es.length, (es[j.val]).u ≠ (es[j.val]).v →
    ((es[j.val]).u = x ∨ (es[j.val]).v = x) →
    (es[idx.val]).weight < (es[j.val]).weight ∨
      ((es[idx.val]).weight = (es[j.val]).weight ∧ idx.val ≤ j.val)

private theorem FramedTriple.with_modifies {α : Type} {w c : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {S : Set ℕ} {Q : α → Memory.State → Prop}
    (h : Memory.FramedTriple w s p c S Q) :
    Memory.FramedTriple w s p c S fun a s' => Memory.Modifies S s s' ∧ Q a s' :=
  Memory.Triple.mono h le_rfl fun _ _ ⟨hm, hq⟩ => ⟨hm, hm, hq⟩

private theorem fits_edges_succ {w s_fr eb m k : ℕ} (h16 : Fits w 16) (hin : eb + 4 * m ≤ s_fr)
    (hfit : Fits w (s_fr + k)) : Fits w (m + 1) := by
  by_cases hm : m = 0
  · rw [hm]; exact h16.of_le (by omega)
  · exact hfit.of_le (by omega)

/-! ## Minimum Incident Edge Selection (`boruvkaMinProg`) -/

private structure UpdateEndArgs where
  edgeBase : ℕ
  minIdxBase : ℕ
  numEdges : ℕ
  edgeIdx : ℕ
  weight : ℕ
  vert : ℕ

private word_enc_structure encUpdateEndArgs : UpdateEndArgs where
  edgeBase : wordWords,
  minIdxBase : wordWords,
  numEdges : wordWords,
  edgeIdx : wordWords,
  weight : wordWords,
  vert : wordWords

private instance : WordEncoding UpdateEndArgs := ⟨6, encUpdateEndArgs⟩

private def boruvkaUpdateEnd (a : UpdateEndArgs) : Memory.Prog Unit := do
  let cur ← Memory.read (a.minIdxBase + a.vert)
  if cur = a.numEdges then
    Memory.write (a.minIdxBase + a.vert) a.edgeIdx
  else do
    let curW ← Memory.read (a.edgeBase + 4 * cur + 2)
    if a.weight < curW then
      Memory.write (a.minIdxBase + a.vert) a.edgeIdx
    else
      pure ()

private def boruvkaUpdateEndSafe (w : ℕ) (a : UpdateEndArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w a.numEdges ∧ Fits w a.edgeIdx ∧ Fits w a.weight ∧
  a.minIdxBase + a.vert < s.frontier ∧
  (s.mem (a.minIdxBase + a.vert) ≠ a.numEdges →
    a.edgeBase + 4 * s.mem (a.minIdxBase + a.vert) + 2 < s.frontier)

private theorem realizes_boruvkaUpdateEnd : Realizes .exact
    boruvkaUpdateEnd WordEncoding.encode WordEncoding.encode
    boruvkaUpdateEndSafe (fun _ _ => 0) := by
  unfold boruvkaUpdateEnd
  realize
  all_goals
    obtain ⟨h16, hm, hk, hwt, hx, hcur⟩ := h
    have hfront := hmem.frontier_fits
    have hmc := hmem.mem_fits (d.minIdxBase + d.vert)
    first
    | (have hcw := hmem.mem_fits (d.edgeBase + 4 * s.mem (d.minIdxBase + d.vert) + 2)
       have hc' := hcur hc
       fits)
    | fits

private theorem boruvkaUpdateEnd_ft {w edgeBase minIdxBase m k wt x : ℕ} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hm : Fits w m) (hk : Fits w k) (hwt : Fits w wt) (hx_lt : minIdxBase + x < s.frontier)
    (hcur : s.mem (minIdxBase + x) ≠ m → edgeBase + 4 * s.mem (minIdxBase + x) + 2 < s.frontier) :
    boruvkaUpdateEndSafe w ⟨edgeBase, minIdxBase, m, k, wt, x⟩ s ∧
    Memory.FramedTriple w s (boruvkaUpdateEnd ⟨edgeBase, minIdxBase, m, k, wt, x⟩) 3
      (Set.Ico (minIdxBase + x) (minIdxBase + x + 1)) fun _ s' =>
        (s'.frontier = s.frontier ∧
        (s.mem (minIdxBase + x) = m → s'.mem (minIdxBase + x) = k) ∧
        (s.mem (minIdxBase + x) ≠ m →
          (wt < s.mem (edgeBase + 4 * s.mem (minIdxBase + x) + 2) →
            s'.mem (minIdxBase + x) = k) ∧
          (¬ wt < s.mem (edgeBase + 4 * s.mem (minIdxBase + x) + 2) →
            s'.mem (minIdxBase + x) = s.mem (minIdxBase + x)))) ∧
        Memory.WellFormed w s' := by
  refine ⟨⟨h16, hm, hk, hwt, hx_lt, hcur⟩, Memory.FramedTriple.wellFormed hwf ?_⟩
  dsimp only [boruvkaUpdateEnd]
  refine Memory.FramedTriple.read_bind hx_lt ?_
  by_cases hcm : s.mem (minIdxBase + x) = m
  · split_ifs
    exact (Memory.FramedTriple.write hx_lt hk (by simp only [Set.mem_Ico]; omega)
      ⟨rfl, fun _ => Function.update_self _ _ _, fun h => absurd hcm h⟩).mono
      (by decide) fun _ _ h => h
  · split_ifs
    refine Memory.FramedTriple.read_bind (hcur hcm) ?_
    by_cases hlt : wt < s.mem (edgeBase + 4 * s.mem (minIdxBase + x) + 2)
    · split_ifs
      exact Memory.FramedTriple.write hx_lt hk (by simp only [Set.mem_Ico]; omega)
        ⟨rfl, fun hm' => absurd hm' hcm, fun _ => ⟨fun _ => Function.update_self _ _ _,
          fun hn => absurd hlt hn⟩⟩
    · split_ifs
      exact (Memory.FramedTriple.pure (c := 0) ⟨rfl, fun hm' => absurd hm' hcm,
        fun _ => ⟨fun hl => absurd hl hlt, fun _ => rfl⟩⟩).mono (by decide) fun _ _ h => h

private structure MinCfg where
  edgeBase : ℕ
  minIdxBase : ℕ
  numEdges : ℕ

private word_enc_structure encMinCfg : MinCfg where
  edgeBase : wordWords,
  minIdxBase : wordWords,
  numEdges : wordWords

private instance : WordEncoding MinCfg := ⟨3, encMinCfg⟩

private def boruvkaMinStep (d : MinCfg × ℕ) : Memory.Prog ℕ := do
  let cfg := d.1
  let k := d.2
  let u ← Memory.read (cfg.edgeBase + 4 * k)
  let v ← Memory.read (cfg.edgeBase + 4 * k + 1)
  if u = v then
    pure (k + 1)
  else do
    let wt ← Memory.read (cfg.edgeBase + 4 * k + 2)
    boruvkaUpdateEnd ⟨cfg.edgeBase, cfg.minIdxBase, cfg.numEdges, k, wt, u⟩
    boruvkaUpdateEnd ⟨cfg.edgeBase, cfg.minIdxBase, cfg.numEdges, k, wt, v⟩
    pure (k + 1)

private def boruvkaMinStepSafe (w : ℕ) (d : MinCfg × ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w d.1.numEdges ∧ Fits w (d.2 + 1) ∧
  d.1.edgeBase + 4 * d.2 + 2 < s.frontier ∧
  (s.mem (d.1.edgeBase + 4 * d.2) ≠ s.mem (d.1.edgeBase + 4 * d.2 + 1) →
    d.1.minIdxBase + s.mem (d.1.edgeBase + 4 * d.2) < s.frontier ∧
    d.1.minIdxBase + s.mem (d.1.edgeBase + 4 * d.2 + 1) < s.frontier ∧
    (s.mem (d.1.minIdxBase + s.mem (d.1.edgeBase + 4 * d.2)) ≠ d.1.numEdges →
      d.1.edgeBase + 4 * s.mem (d.1.minIdxBase + s.mem (d.1.edgeBase + 4 * d.2)) + 2 <
        s.frontier) ∧
    (s.mem (d.1.minIdxBase + s.mem (d.1.edgeBase + 4 * d.2 + 1)) ≠ d.1.numEdges →
      d.1.edgeBase + 4 * s.mem (d.1.minIdxBase + s.mem (d.1.edgeBase + 4 * d.2 + 1)) + 2 <
        s.frontier))

private theorem realizes_boruvkaMinStep : Realizes .exact
    boruvkaMinStep WordEncoding.encode WordEncoding.encode
    boruvkaMinStepSafe (fun _ _ => 0) := by
  unfold boruvkaMinStep
  realize [realizes_boruvkaUpdateEnd]
  all_goals
    obtain ⟨h16, hm, hk1, hbound, hne⟩ := h
    have hfront := hmem.frontier_fits
    have hmu := hmem.mem_fits (d.1.edgeBase + 4 * d.2)
    have hmv := hmem.mem_fits (d.1.edgeBase + 4 * d.2 + 1)
    first
    | fits
    | (dsimp only [boruvkaUpdateEndSafe]
       exact ⟨h16, hm, hk1.of_le (by omega), hmem.mem_fits (d.1.edgeBase + 4 * d.2 + 2),
         (hne hc).1, (hne hc).2.2.1⟩)
    | (have hu_ft := (boruvkaUpdateEnd_ft (m := d.1.numEdges) (k := d.2) h16 hmem hm
          (hk1.of_le (by omega)) (hmem.mem_fits (d.1.edgeBase + 4 * d.2 + 2))
          (hne hc).1 (hne hc).2.2.1).2
       have hu_fr := (framedTriple_iff_realization.mp hu_ft).2.2.2.1.1
       have hu_mod := (framedTriple_iff_realization.mp hu_ft).2.2.1
       have hmem_v : ((Memory.spec 0).clientState s
           (boruvkaUpdateEnd ⟨d.1.edgeBase, d.1.minIdxBase, d.1.numEdges, d.2,
             s.mem (d.1.edgeBase + 4 * d.2 + 2), s.mem (d.1.edgeBase + 4 * d.2)⟩)).mem
             (d.1.minIdxBase + s.mem (d.1.edgeBase + 4 * d.2 + 1)) =
           s.mem (d.1.minIdxBase + s.mem (d.1.edgeBase + 4 * d.2 + 1)) :=
         hu_mod.mem_eq_of_not_mem (hne hc).2.1
           (by simp only [Set.mem_Ico]; intro h; exact hc (by omega))
       dsimp only [boruvkaUpdateEndSafe]
       refine ⟨h16, hm, hk1.of_le (by omega), hmem.mem_fits (d.1.edgeBase + 4 * d.2 + 2),
         by rw [hu_fr]; exact (hne hc).2.1, fun hne2 => ?_⟩
       rw [hu_fr]; rw [hmem_v] at hne2 ⊢; exact (hne hc).2.2.2 hne2)

private def vertOpt {n : ℕ} (minIdxBase k : ℕ) (es : List (IndexedEdge n))
    (mem : ℕ → ℕ) (x : Fin n) : Prop :=
  (mem (minIdxBase + x.val) = es.length ∧
    ∀ j (hj : j < es.length), j < k → (es[j]'hj).u ≠ (es[j]'hj).v →
      (es[j]'hj).u ≠ x ∧ (es[j]'hj).v ≠ x) ∨
  ∃ i, ∃ (_ : i < k), ∃ (hl : i < es.length), mem (minIdxBase + x.val) = i ∧
    (es[i]'hl).u ≠ (es[i]'hl).v ∧
    ((es[i]'hl).u = x ∨ (es[i]'hl).v = x) ∧
    ∀ j (hj : j < es.length), j < k → (es[j]'hj).u ≠ (es[j]'hj).v →
      ((es[j]'hj).u = x ∨ (es[j]'hj).v = x) →
      (es[i]'hl).weight < (es[j]'hj).weight ∨
        ((es[i]'hl).weight = (es[j]'hj).weight ∧ i ≤ j)

private theorem vertOpt_step_upd {n minIdxBase edgeBase k : ℕ} {es : List (IndexedEdge n)}
    (hk : k < es.length) (hne_uv : (es[k]'hk).u ≠ (es[k]'hk).v)
    {mem₁ mem₂ : ℕ → ℕ}
    (hin : HoldsIndexedEdges edgeBase es mem₁)
    {z : Fin n} (hopt : vertOpt minIdxBase k es mem₁ z)
    (hinc_z : (es[k]'hk).u = z ∨ (es[k]'hk).v = z)
    (hm_upd : mem₁ (minIdxBase + z.val) = es.length → mem₂ (minIdxBase + z.val) = k)
    (hlt_upd : mem₁ (minIdxBase + z.val) ≠ es.length →
      ((es[k]'hk).weight < mem₁ (edgeBase + 4 * mem₁ (minIdxBase + z.val) + 2) →
        mem₂ (minIdxBase + z.val) = k) ∧
      (¬ (es[k]'hk).weight < mem₁ (edgeBase + 4 * mem₁ (minIdxBase + z.val) + 2) →
        mem₂ (minIdxBase + z.val) = mem₁ (minIdxBase + z.val))) :
    vertOpt minIdxBase (k + 1) es mem₂ z := by
  rcases hopt with ⟨hm_z, hnone⟩ | ⟨i, hi, hl, heq, hne_i, hinc_i, hbest⟩
  · refine .inr ⟨k, Nat.lt_succ_self k, hk, hm_upd hm_z, hne_uv, hinc_z,
        fun j hj _ hne_j hinc_j => ?_⟩
    by_cases hjk : j = k
    · subst j; exact .inr ⟨rfl, le_rfl⟩
    · exact hinc_j.elim (fun h => absurd h (hnone j hj (by omega) hne_j).1) fun h =>
        absurd h (hnone j hj (by omega) hne_j).2
  · have him : mem₁ (minIdxBase + z.val) ≠ es.length := by rw [heq]; omega
    have hwt_cur : mem₁ (edgeBase + 4 * mem₁ (minIdxBase + z.val) + 2) = (es[i]'hl).weight := by
      rw [heq]; exact (hin i hl).2.2.1
    by_cases hlt_w : (es[k]'hk).weight < (es[i]'hl).weight
    · refine .inr ⟨k, Nat.lt_succ_self k, hk, (hlt_upd him).1 (by rw [hwt_cur]; exact hlt_w),
        hne_uv, hinc_z, fun j hj _ hne_j hinc_j => ?_⟩
      by_cases hjk : j = k
      · subst j; exact .inr ⟨rfl, le_rfl⟩
      · exact .inl ((hbest j hj (by omega) hne_j hinc_j).elim (lt_trans hlt_w)
          fun ⟨heq_ij, _⟩ => lt_of_lt_of_eq hlt_w heq_ij)
    · refine .inr ⟨i, by omega, hl, ((hlt_upd him).2 (by rw [hwt_cur]; exact hlt_w)).trans heq,
        hne_i, hinc_i, fun j hj _ hne_j hinc_j => ?_⟩
      by_cases hjk : j = k
      · subst j; exact (Nat.eq_or_lt_of_le (Nat.le_of_not_lt hlt_w)).elim
          (fun h => .inr ⟨h, hi.le⟩) .inl
      · exact hbest j hj (by omega) hne_j hinc_j

private theorem vertOpt_step_other {n minIdxBase k : ℕ} {es : List (IndexedEdge n)}
    (hk : k < es.length) {mem₁ mem₂ : ℕ → ℕ} {x : Fin n}
    (hxu : x ≠ (es[k]'hk).u) (hxv : x ≠ (es[k]'hk).v)
    (heq_x : mem₂ (minIdxBase + x.val) = mem₁ (minIdxBase + x.val))
    (hopt : vertOpt minIdxBase k es mem₁ x) : vertOpt minIdxBase (k + 1) es mem₂ x := by
  rcases hopt with ⟨hm, hn⟩ | ⟨i, hi, hl, heq, hne, hinc, hb⟩
  · exact .inl ⟨heq_x.trans hm, fun j hj _ hne => by
      by_cases hjk : j = k
      · subst j; exact ⟨fun h => hxu h.symm, fun h => hxv h.symm⟩
      · exact hn j hj (by omega) hne⟩
  · exact .inr ⟨i, by omega, hl, heq_x.trans heq, hne, hinc, fun j hj _ hnej hincj => by
      by_cases hjk : j = k
      · subst j; exact hincj.elim (fun h => absurd h.symm hxu) fun h => absurd h.symm hxv
      · exact hb j hj (by omega) hnej hincj⟩

private theorem boruvkaMin_iter_spec {w n edgeBase minIdxBase : ℕ}
    {es : List (IndexedEdge n)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hin_lt : edgeBase + 4 * es.length ≤ minIdxBase)
    (hmin_lt : minIdxBase + n ≤ s.frontier)
    (hfit_m1 : Fits w (es.length + 1))
    (hinit : ∀ x : Fin n, s.mem (minIdxBase + x.val) = es.length) :
    let S := Set.Ico minIdxBase (minIdxBase + n)
    iterationSafe boruvkaMinStep boruvkaMinStepSafe w ⟨edgeBase, minIdxBase, es.length⟩
      es.length 0 s ∧
    Memory.FramedTriple w s (iterate boruvkaMinStep ⟨edgeBase, minIdxBase, es.length⟩ es.length 0)
      (9 * es.length) S fun _ s' =>
        s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        ∀ x : Fin n, vertOpt minIdxBase es.length es s'.mem x := by
  let S := Set.Ico minIdxBase (minIdxBase + n)
  let inv (k st : ℕ) (t : Memory.State) : Prop :=
    st = k ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t ∧
    HoldsIndexedEdges edgeBase es t.mem ∧ ∀ x : Fin n, vertOpt minIdxBase k es t.mem x
  obtain ⟨hsafe, hvh, hcost, hmod, hinv⟩ :=
    iterate_potential_spec boruvkaMinStep boruvkaMinStepSafe w ⟨edgeBase, minIdxBase, es.length⟩ 9
      es.length inv (fun _ _ _ => 0) S (fun k hk st t ⟨hst_eq, htfr, hwt, hin_t, hopt⟩ => by
        subst st
        obtain ⟨hu, hv, hw, _⟩ := hin_t k hk
        let ek := es[k]'hk
        have hcur_bound : ∀ x : Fin n, t.mem (minIdxBase + x.val) ≠ es.length →
            edgeBase + 4 * t.mem (minIdxBase + x.val) + 2 < t.frontier := fun x hne => by
          rcases hopt x with ⟨heq, _⟩ | ⟨i, _, _, heq, _⟩
          · exact absurd heq hne
          · rw [heq, htfr]; omega
        have hsafe : boruvkaMinStepSafe w (⟨edgeBase, minIdxBase, es.length⟩, k) t := by
          dsimp only [boruvkaMinStepSafe]
          refine ⟨h16, hfit_m1.of_le (by omega), hfit_m1.of_le (by omega),
            by rw [htfr]; omega, fun _ => ?_⟩
          rw [hu, hv]
          exact ⟨by rw [htfr]; omega, by rw [htfr]; omega, hcur_bound ek.u, hcur_bound ek.v⟩
        have hft : Memory.FramedTriple w t (boruvkaMinStep (⟨edgeBase, minIdxBase, es.length⟩, k))
            9 S fun r t' => r = k + 1 ∧ t'.frontier = t.frontier ∧ Memory.WellFormed w t' ∧
              HoldsIndexedEdges edgeBase es t'.mem ∧
              ∀ x : Fin n, vertOpt minIdxBase (k + 1) es t'.mem x := by
          dsimp only [boruvkaMinStep]
          refine (Memory.FramedTriple.read_bind (c := 8) (by rw [htfr]; omega)
            (Memory.FramedTriple.read_bind (c := 7) (by rw [htfr]; omega) ?_)).mono
            (by decide) fun _ _ h => h
          by_cases heq_uv : ek.u = ek.v
          · simp only [show t.mem (edgeBase + 4 * k) = t.mem (edgeBase + 4 * k + 1) by
              rw [hu, hv]; exact congrArg Fin.val heq_uv, ↓reduceIte]
            refine (Memory.FramedTriple.pure (c := 0) ⟨rfl, rfl, hwt, hin_t, fun x =>
              (hopt x).elim (fun ⟨hm, hn⟩ => .inl ⟨hm, fun j hj _ hne => by
                by_cases hjk : j = k
                · subst j; exact absurd heq_uv hne
                · exact hn j hj (by omega) hne⟩)
              fun ⟨i, _, hl, heq, hne, hinc, hb⟩ => .inr ⟨i, by omega, hl, heq, hne, hinc,
                fun j hj _ hnej hincj => by
                  by_cases hjk : j = k
                  · subst j; exact absurd heq_uv hnej
                  · exact hb j hj (by omega) hnej hincj⟩⟩).mono (by decide) fun _ _ h => h
          · simp only [show t.mem (edgeBase + 4 * k) ≠ t.mem (edgeBase + 4 * k + 1) by
              rw [hu, hv]; exact fun h => heq_uv (Fin.ext h), ↓reduceIte]
            refine Memory.FramedTriple.read_bind (c := 6) (by rw [htfr]; omega) ?_
            rw [hu, hv, hw]
            have hwt_fit : Fits w ek.weight := by rw [← hw]; exact hwt.mem_fits _
            have sub_S (z : Fin n) : Set.Ico (minIdxBase + z.val) (minIdxBase + z.val + 1) ⊆ S :=
              fun _ ⟨h1, h2⟩ => ⟨by omega, by omega⟩
            refine Memory.FramedTriple.bind_same (c₂ := 3)
              (((FramedTriple.with_modifies (boruvkaUpdateEnd_ft (m := es.length) (k := k) h16 hwt
                (hfit_m1.of_le (by omega)) (hfit_m1.of_le (by omega)) hwt_fit (by rw [htfr]; omega)
                (hcur_bound ek.u)).2).frame_mono (sub_S ek.u)).mono le_rfl fun _ t₁
                ⟨hmod1, ⟨hfr1, hu1_m, hu1_lt⟩, hwf1⟩ => ?_)
            have ht1_ne {a} (ha : a < t.frontier) (hne : a ≠ minIdxBase + ek.u.val) :
                t₁.mem a = t.mem a :=
              hmod1.mem_eq_of_not_mem ha (by simp only [Set.mem_Ico]; omega)
            have hv_keep : t₁.mem (minIdxBase + ek.v.val) = t.mem (minIdxBase + ek.v.val) :=
              ht1_ne (by rw [htfr]; omega) (fun h => heq_uv (Fin.ext (by omega)))
            refine Memory.FramedTriple.bind_same (c₂ := 0)
              (((FramedTriple.with_modifies (boruvkaUpdateEnd_ft (m := es.length) (k := k) h16
                hwf1 (hfit_m1.of_le (by omega)) (hfit_m1.of_le (by omega)) hwt_fit
                (by rw [hfr1, htfr]; omega) (by rw [hv_keep, hfr1]; exact hcur_bound ek.v)).2
                ).frame_mono (sub_S ek.v)).mono le_rfl fun _ t₂
                ⟨hmod2, ⟨hfr2, hu2_m, hu2_lt⟩, hwf2⟩ => ?_)
            have ht2_ne {a} (ha : a < t₁.frontier) (hne : a ≠ minIdxBase + ek.v.val) :
                t₂.mem a = t₁.mem a :=
              hmod2.mem_eq_of_not_mem ha (by simp only [Set.mem_Ico]; omega)
            refine Memory.FramedTriple.pure ⟨rfl, hfr2.trans hfr1, hwf2,
              hin_t.congr (fun a _ ha => (ht2_ne (by rw [hfr1, htfr]; omega) (by omega)).trans
                (ht1_ne (by rw [htfr]; omega) (by omega))), fun x => ?_⟩
            by_cases hxu : x = ek.u
            · subst x
              have hku : t₂.mem (minIdxBase + ek.u.val) = t₁.mem (minIdxBase + ek.u.val) :=
                ht2_ne (by rw [hfr1, htfr]; omega) (fun h => heq_uv (Fin.ext (by omega)))
              exact vertOpt_step_upd hk heq_uv hin_t (hopt ek.u) (.inl rfl)
                (fun hm => hku.trans (hu1_m hm)) (fun hm =>
                  ⟨fun h => hku.trans ((hu1_lt hm).1 h), fun h => hku.trans ((hu1_lt hm).2 h)⟩)
            · by_cases hxv : x = ek.v
              · subst x
                have hwc : t.mem (minIdxBase + ek.v.val) ≠ es.length →
                    t₁.mem (edgeBase + 4 * t₁.mem (minIdxBase + ek.v.val) + 2) =
                      t.mem (edgeBase + 4 * t.mem (minIdxBase + ek.v.val) + 2) := fun hmv =>
                  (hopt ek.v).elim (fun h => absurd h.1 hmv) fun ⟨_, _, _, heq, _⟩ => by
                    rw [hv_keep, heq]; exact ht1_ne (by rw [htfr]; omega) (by omega)
                exact vertOpt_step_upd hk heq_uv hin_t (hopt ek.v) (.inr rfl)
                  (fun hm => hu2_m (hv_keep ▸ hm))
                  (fun hm => ⟨fun h => (hu2_lt (hv_keep ▸ hm)).1 (by rw [hwc hm]; exact h),
                    fun h => ((hu2_lt (hv_keep ▸ hm)).2 (by rw [hwc hm]; exact h)).trans hv_keep⟩)
              · exact vertOpt_step_other hk hxu hxv
                  ((ht2_ne (by rw [hfr1, htfr]; omega) (fun h => hxv (Fin.ext (by omega)))).trans
                    (ht1_ne (by rw [htfr]; omega) (fun h => hxu (Fin.ext (by omega))))) (hopt x)
        obtain ⟨hvh, hcost, hmod, hres, hfr', hwf', hin', hopt'⟩ :=
          framedTriple_iff_realization.mp hft
        exact ⟨hsafe, hvh, hcost, hmod, ⟨hres, hfr'.trans htfr, hwf', hin', hopt'⟩⟩)
      0 s ⟨rfl, rfl, hwf, hin, fun x => .inl ⟨hinit x, fun _ _ h0 => absurd h0 (Nat.not_lt_zero _)⟩⟩
  exact ⟨hsafe, framedTriple_iff_realization.mpr
    ⟨hvh, by simpa only [Nat.add_zero, Nat.zero_add] using hcost,
      hmod, hinv.2.1, hinv.2.2.1, hinv.2.2.2.2⟩⟩

/-- Computes for each vertex `x < g.numVertices` the index `< g.numEdges` of its lightest
incident non-loop edge (tie-broken by smallest index), or `g.numEdges` if none exists. -/
def boruvkaMinProg (g : GraphSlice) : Memory.Prog ℕ := do
  let minIdxBlk ← Memory.allocBlockDirty g.numVertices
  let _ ← fillConstProg minIdxBlk.base g.numEdges g.numVertices
  let _ ← iterate boruvkaMinStep ⟨g.edgeBase, minIdxBlk.base, g.numEdges⟩ g.numEdges 0
  pure minIdxBlk.base

private theorem boruvkaMinProg_aux {w n edgeBase : ℕ} {es : List (IndexedEdge n)}
    {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hin_lt : edgeBase + 4 * es.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + (n + 1))) :
    let minIdxBase := s.frontier
    let s₁ : Memory.State := ⟨s.mem, minIdxBase + n⟩
    let s₂ := (Memory.spec 0).clientState s₁ (fillConstProg minIdxBase es.length n)
    iterationSafe boruvkaMinStep boruvkaMinStepSafe w ⟨edgeBase, minIdxBase, es.length⟩
      es.length 0 s₂ ∧
    Memory.FramedTriple w s (boruvkaMinProg ⟨n, es.length, edgeBase⟩) (9 * es.length + n + 1) ∅
      fun minIdxBase s' => minIdxBase = s.frontier ∧ s'.frontier = s.frontier + n ∧
        Memory.WellFormed w s' ∧ ∀ x : Fin n, vertOpt minIdxBase es.length es s'.mem x := by
  let minIdxBase := s.frontier
  let s₁ : Memory.State := ⟨s.mem, minIdxBase + n⟩
  have hfit_n : Fits w n := hfit.of_le (by omega)
  have hfit_m1 : Fits w (es.length + 1) := fits_edges_succ h16 hin_lt hfit
  have hfit_s1 : Fits w (minIdxBase + n) := hfit.of_le (by dsimp only [minIdxBase]; omega)
  have hfill_ft := fillConstProg_spec (s := s₁) (base := minIdxBase) (val := es.length)
    (count := n) ⟨hfit_s1, hwf.mem_fits⟩ (hfit_m1.of_le (by omega)) hfit_n le_rfl
  obtain ⟨_, _, hmod_fill, hfr_fill, hwf₂, hvals_fill⟩ := framedTriple_iff_realization.mp hfill_ft
  have hin_of_mod {t : Memory.State} (hmod : Memory.Modifies (Set.Ico minIdxBase (minIdxBase + n))
      s₁ t) : HoldsIndexedEdges edgeBase es t.mem :=
    hin.congr fun a _ ha => hmod.mem_eq_of_not_mem (by dsimp only [s₁, minIdxBase]; omega)
      (by simp only [Set.mem_Ico]; dsimp only [minIdxBase]; omega)
  refine ⟨(boruvkaMin_iter_spec h16 hwf₂ (hin_of_mod hmod_fill) hin_lt (by rw [hfr_fill])
    hfit_m1 fun x => hvals_fill x.val x.isLt).1,
    ((Memory.FramedTriple.allocBlockDirty_bind hfit_s1 (Memory.FramedTriple.bind_same
      (c₂ := 9 * es.length) ((FramedTriple.with_modifies hfill_ft).mono le_rfl
        fun _ t₁ ⟨hmod₁, htfr₁, hwt₁, hvals₁⟩ => Memory.FramedTriple.bind_same (c₂ := 0)
          ((boruvkaMin_iter_spec h16 hwt₁ (hin_of_mod hmod₁) hin_lt (by rw [htfr₁]) hfit_m1
            fun x => hvals₁ x.val x.isLt).2.mono le_rfl fun _ s' ⟨hsfr', hwf', hopt'⟩ =>
              Memory.FramedTriple.pure ⟨rfl, hsfr'.trans htfr₁, hwf', hopt'⟩)))).mono
      (by omega) fun _ _ h => h).frame_empty_of_ge_frontier
      (S := Set.Ico minIdxBase (minIdxBase + n)) fun _ ha => ha.1⟩

/-- Uniform `Realizes .exact` certificate for `boruvkaMinProg` with `work = 0`. -/
theorem realizes_boruvkaMinProg : Realizes .exact
    boruvkaMinProg WordEncoding.encode WordEncoding.encode
    (fun w g s => Fits w 16 ∧ g.edgeBase + 4 * g.numEdges ≤ s.frontier ∧
      Fits w (s.frontier + (g.numVertices + 1)) ∧
      ∀ j < g.numEdges,
        s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
        s.mem (g.edgeBase + 4 * j + 1) < g.numVertices)
    (fun _ _ => 0) := by
  have hraw : Realizes .exact boruvkaMinProg WordEncoding.encode WordEncoding.encode
      (fun w g s =>
        let minIdxBase := s.frontier
        let s₁ : Memory.State := ⟨s.mem, minIdxBase + g.numVertices⟩
        let s₂ := (Memory.spec 0).clientState s₁ (fillConstProg minIdxBase g.numEdges g.numVertices)
        iterationSafe boruvkaMinStep boruvkaMinStepSafe w
          ⟨g.edgeBase, minIdxBase, g.numEdges⟩ g.numEdges 0 s₂)
      (fun _ _ => 0) := by
    unfold boruvkaMinProg
    realize [realizes_allocBlockDirty, realizes_fillConstProg, realizes_boruvkaMinStep]
    · exact le_rfl
    · exact iterationSafe_imp h (fun _ => rfl) (fun _ _ hs => hs)
  refine hraw.consequence (fun w g s _ hmem ⟨h16, hin_lt, hfit, hedges⟩ => ?_)
    (fun _ _ => le_rfl)
  obtain ⟨es, hlen, hin⟩ := exists_indexedEdges_of_mem_lt hedges
  have haux := boruvkaMinProg_aux h16 hmem hin (by rw [hlen]; exact hin_lt) hfit
  rw [← hlen]; exact haux.1

/-- Framed specification for `boruvkaMinProg`: allocates a length-`n` array at `s.frontier`
recording each vertex's minimum-weight non-loop incident edge index (or `es.length`), leaving all
cells below `s.frontier` untouched, in at most `9 * es.length + n + 1` memory operations. -/
theorem boruvkaMinProg_spec {w n edgeBase : ℕ} {es : List (IndexedEdge n)}
    {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hin_lt : edgeBase + 4 * es.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + (n + 1))) :
    Memory.FramedTriple w s (boruvkaMinProg ⟨n, es.length, edgeBase⟩)
      (9 * es.length + n + 1) ∅ fun minIdxBase s' =>
        minIdxBase = s.frontier ∧
        s'.frontier = s.frontier + n ∧
        Memory.WellFormed w s' ∧
        ∀ x : Fin n,
          (s'.mem (minIdxBase + x.val) = es.length ∧
            ∀ j : Fin es.length, (es[j.val]).u ≠ (es[j.val]).v →
              (es[j.val]).u ≠ x ∧ (es[j.val]).v ≠ x) ∨
          ∃ idx : Fin es.length, s'.mem (minIdxBase + x.val) = idx.val ∧
            (es[idx.val]).u ≠ (es[idx.val]).v ∧
            ((es[idx.val]).u = x ∨ (es[idx.val]).v = x) ∧
            ∀ j : Fin es.length, (es[j.val]).u ≠ (es[j.val]).v →
              ((es[j.val]).u = x ∨ (es[j.val]).v = x) →
              (es[idx.val]).weight < (es[j.val]).weight ∨
                ((es[idx.val]).weight = (es[j.val]).weight ∧ idx.val ≤ j.val) :=
  (boruvkaMinProg_aux h16 hwf hin hin_lt hfit).2.mono le_rfl fun _ _ ⟨h1, h2, h3, hopt⟩ =>
    ⟨h1, h2, h3, fun x => match hopt x with
      | .inl ⟨heq, hnone⟩ => .inl ⟨heq, fun j => hnone j.val j.isLt j.isLt⟩
      | .inr ⟨i, hi, _, heq, hne, hinc, hbest⟩ =>
        .inr ⟨⟨i, hi⟩, heq, hne, hinc, fun j => hbest j.val j.isLt j.isLt⟩⟩

/-! ## Deduplicated Selection Materialization (`boruvkaSelectProg`) -/

private structure CollectCfg where
  edgeBase : ℕ
  minIdxBase : ℕ
  usedBase : ℕ
  selBase : ℕ
  numEdges : ℕ

private word_enc_structure encCollectCfg : CollectCfg where
  edgeBase : wordWords,
  minIdxBase : wordWords,
  usedBase : wordWords,
  selBase : wordWords,
  numEdges : wordWords

private instance : WordEncoding CollectCfg := ⟨5, encCollectCfg⟩

private structure CollectState where
  vertIdx : ℕ
  selLen : ℕ

private word_enc_structure encCollectState : CollectState where
  vertIdx : wordWords,
  selLen : wordWords

private instance : WordEncoding CollectState := ⟨2, encCollectState⟩

private def boruvkaCollectStep (d : CollectCfg × CollectState) : Memory.Prog CollectState := do
  let cfg := d.1
  let st := d.2
  let idx ← Memory.read (cfg.minIdxBase + st.vertIdx)
  if idx < cfg.numEdges then do
    let flag ← Memory.read (cfg.usedBase + idx)
    if flag = 0 then do
      Memory.write (cfg.usedBase + idx) 1
      Memory.copy (cfg.edgeBase + 4 * idx) (cfg.selBase + 4 * st.selLen) 4
      pure ⟨st.vertIdx + 1, st.selLen + 1⟩
    else
      pure ⟨st.vertIdx + 1, st.selLen⟩
  else
    pure ⟨st.vertIdx + 1, st.selLen⟩

private def boruvkaCollectStepSafe (w : ℕ) (d : CollectCfg × CollectState)
    (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w d.1.numEdges ∧ Fits w (d.2.vertIdx + 1) ∧ Fits w (d.2.selLen + 1) ∧
  d.1.minIdxBase + d.2.vertIdx < s.frontier ∧
  (s.mem (d.1.minIdxBase + d.2.vertIdx) < d.1.numEdges →
    d.1.usedBase + s.mem (d.1.minIdxBase + d.2.vertIdx) < s.frontier ∧
    (s.mem (d.1.usedBase + s.mem (d.1.minIdxBase + d.2.vertIdx)) = 0 →
      d.1.edgeBase + 4 * s.mem (d.1.minIdxBase + d.2.vertIdx) + 3 < s.frontier ∧
      d.1.selBase + 4 * d.2.selLen + 3 < s.frontier))

private theorem realizes_boruvkaCollectStep : Realizes .exact
    boruvkaCollectStep WordEncoding.encode WordEncoding.encode
    boruvkaCollectStepSafe (fun _ _ => 0) := by
  unfold boruvkaCollectStep
  realize [realizes_copy]
  all_goals
    obtain ⟨h16, hm, hu1, hsl1, hmin_lt, hguard⟩ := h
    have hfront := hmem.frontier_fits
    have hmidx := hmem.mem_fits (d.1.minIdxBase + d.2.vertIdx)
    first
    | (have hg := hguard (by assumption)
       have hc2 := hg.2 (by assumption)
       omega)
    | (have hg := hguard (by assumption)
       have hmflag := hmem.mem_fits (d.1.usedBase + s.mem (d.1.minIdxBase + d.2.vertIdx))
       fits)
    | fits

private theorem boruvkaCollect_iter_word_spec {w n m edgeBase minIdxBase usedBase selBase : ℕ}
    {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hmin_lt : minIdxBase + n ≤ s.frontier)
    (hused_lt : usedBase + m ≤ s.frontier)
    (hused_disj_in : edgeBase + 4 * m ≤ usedBase)
    (hused_disj_min : minIdxBase + n ≤ usedBase)
    (hused_init : ∀ j < m, s.mem (usedBase + j) = 0)
    (hsel_lt : selBase + 4 * n ≤ s.frontier)
    (hsel_disj_used : usedBase + m ≤ selBase)
    (hsel_disj_in : edgeBase + 4 * m ≤ selBase)
    (hfit_n1 : Fits w (n + 1)) (hfit_m1 : Fits w (m + 1)) :
    let cfg : CollectCfg := ⟨edgeBase, minIdxBase, usedBase, selBase, m⟩
    let S := Set.Ico usedBase (usedBase + m) ∪ Set.Ico selBase (selBase + 4 * n)
    iterationSafe boruvkaCollectStep boruvkaCollectStepSafe w cfg n ⟨0, 0⟩ s ∧
    Memory.FramedTriple w s (iterate boruvkaCollectStep cfg n ⟨0, 0⟩) (11 * n) S fun res s' =>
      res.vertIdx = n ∧ res.selLen ≤ n ∧
      s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
      ∃ selIdxs : List (Fin m),
        selIdxs.length = res.selLen ∧
        selIdxs.Nodup ∧
        (∀ i (hi : i < selIdxs.length), ∀ q < 4,
          s'.mem (selBase + 4 * i + q) = s.mem (edgeBase + 4 * selIdxs[i].val + q)) ∧
        (∀ idx ∈ selIdxs, ∃ x < n, s.mem (minIdxBase + x) = idx.val) ∧
        ∀ x < n, ∀ hlt : s.mem (minIdxBase + x) < m,
          (⟨s.mem (minIdxBase + x), hlt⟩ : Fin m) ∈ selIdxs := by
  let cfg : CollectCfg := ⟨edgeBase, minIdxBase, usedBase, selBase, m⟩
  let S := Set.Ico usedBase (usedBase + m) ∪ Set.Ico selBase (selBase + 4 * n)
  let inv (k : ℕ) (st : CollectState) (t : Memory.State) : Prop :=
    st.vertIdx = k ∧ st.selLen ≤ k ∧ k ≤ n ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t ∧
    (∀ j < m, t.mem (usedBase + j) = 0 ∨ t.mem (usedBase + j) = 1) ∧
    (∀ a < usedBase, t.mem a = s.mem a) ∧
    ∃ selIdxs : List (Fin m), selIdxs.length = st.selLen ∧ selIdxs.Nodup ∧
      (∀ i (hi : i < selIdxs.length), ∀ q < 4,
        t.mem (selBase + 4 * i + q) = s.mem (edgeBase + 4 * selIdxs[i].val + q)) ∧
      (∀ idx : Fin m, idx ∈ selIdxs ↔ t.mem (usedBase + idx.val) = 1) ∧
      (∀ idx ∈ selIdxs, ∃ x < k, s.mem (minIdxBase + x) = idx.val) ∧
      ∀ x < k, ∀ hlt : s.mem (minIdxBase + x) < m,
        (⟨s.mem (minIdxBase + x), hlt⟩ : Fin m) ∈ selIdxs
  obtain ⟨hsafe, hvh, hcost, hmod, hvert, hle, _, hfr, hwf', _, _, selIdxs, hsl_len, hnd, hvals, _,
      hsrc, hcov⟩ :=
    iterate_potential_spec boruvkaCollectStep boruvkaCollectStepSafe w cfg 11 n inv (fun _ _ _ => 0)
      S (fun k hk st t ⟨hk_eq, hsl_le, _, htfr, hwt, hrange, hbelow,
          selIdxs, hsl_len, hnd, hsel_vals, hused_iff, hsrc, hcov⟩ => by
        rcases st with ⟨u_st, selLen⟩
        dsimp only at hk_eq hsl_le hsl_len; subst u_st
        have hidx_eq : t.mem (minIdxBase + k) = s.mem (minIdxBase + k) := hbelow _ (by omega)
        let idx := s.mem (minIdxBase + k)
        have hkeep_inv (hk_cov : ∀ hlt : s.mem (minIdxBase + k) < m,
            (⟨s.mem (minIdxBase + k), hlt⟩ : Fin m) ∈ selIdxs) :
            inv (k + 1) ⟨k + 1, selLen⟩ t := by
          dsimp only [inv]
          refine ⟨rfl, by omega, hk, htfr, hwt, hrange, hbelow, selIdxs, hsl_len, hnd, hsel_vals,
            hused_iff, fun id' hid' => let ⟨x, hx, hmx⟩ := hsrc id' hid'; ⟨x, by omega, hmx⟩,
            fun x hx hlt => ?_⟩
          by_cases hxk : x = k
          · rcases hxk with rfl; exact hk_cov hlt
          · exact hcov x (by omega) hlt
        have hsafe : boruvkaCollectStepSafe w (cfg, ⟨k, selLen⟩) t := by
          dsimp only [boruvkaCollectStepSafe, cfg]
          refine ⟨h16, hfit_m1.of_le (by omega), hfit_n1.of_le (by omega), hfit_n1.of_le (by omega),
            by rw [htfr]; omega, fun hlt => ?_⟩
          rw [hidx_eq] at hlt ⊢
          exact ⟨by rw [htfr]; omega, fun _ => ⟨by rw [htfr]; omega, by rw [htfr]; omega⟩⟩
        have hft : Memory.FramedTriple w t (boruvkaCollectStep (cfg, ⟨k, selLen⟩)) 11 S
            fun st' t' => inv (k + 1) st' t' := by
          dsimp only [boruvkaCollectStep, cfg]
          refine (Memory.FramedTriple.read_bind (c := 10) (by rw [htfr]; omega) ?_).mono
            (by decide) fun _ _ h => h
          rw [hidx_eq]
          by_cases hlt_m : idx < m
          · have hlt_m' : s.mem (minIdxBase + k) < m := hlt_m
            split_ifs
            refine (Memory.FramedTriple.read_bind (c := 9) (by rw [htfr]; omega) ?_).mono
              (by decide) fun _ _ h => h
            let idxFin : Fin m := ⟨idx, hlt_m⟩
            by_cases hflag0 : t.mem (usedBase + idx) = 0
            · have hflag0' : t.mem (usedBase + s.mem (minIdxBase + k)) = 0 := hflag0
              split_ifs
              refine (Memory.FramedTriple.write_bind_of_mem (c := 8) (by rw [htfr]; omega)
                (h16.of_le (by omega)) (by dsimp only [S]; exact Or.inl ⟨by omega, by omega⟩)
                ?_).mono (by decide) fun _ _ h => h
              let t₁ : Memory.State := ⟨Function.update t.mem (usedBase + idx) 1, t.frontier⟩
              have hwf_t1 : Memory.WellFormed w t₁ := ⟨hwt.frontier_fits, fun a => by
                dsimp only [t₁]; by_cases ha : a = usedBase + idx
                · rw [ha, Function.update_self]; exact h16.of_le (by omega)
                · rw [Function.update_of_ne ha]; exact hwt.mem_fits a⟩
              have hcopy_raw : Memory.FramedTriple w t₁
                  (Memory.copy (edgeBase + 4 * idx) (selBase + 4 * selLen) 4) 8
                  (Set.Ico (selBase + 4 * selLen) (selBase + 4 * selLen + 4)) fun _ s' =>
                    s'.frontier = t₁.frontier ∧ Memory.WellFormed w s' ∧
                    ∀ q < 4, s'.mem (selBase + 4 * selLen + q) = t₁.mem (edgeBase + 4 * idx + q) :=
                ((Memory.FramedTriple.copy (.inl (by omega)) (by dsimp only [t₁]; rw [htfr]; omega)
                  (by dsimp only [t₁]; rw [htfr]; omega) (fun _ _ => hwf_t1.mem_fits _)
                  (Q := fun _ s' => s'.frontier = t₁.frontier ∧ ∀ q < 4,
                    s'.mem (selBase + 4 * selLen + q) = t₁.mem (edgeBase + 4 * idx + q))
                  ⟨rfl, fun q hq => ArrayCopy.copyPrefix_read hq⟩).wellFormed hwf_t1).mono
                  (by decide) fun _ _ ⟨⟨hfr_c, hvals_c⟩, hwf_c⟩ => ⟨hfr_c, hwf_c, hvals_c⟩
              refine Memory.FramedTriple.bind_same (c₂ := 0)
                (((FramedTriple.with_modifies hcopy_raw).frame_mono
                  (show Set.Ico (selBase + 4 * selLen) (selBase + 4 * selLen + 4) ⊆ S from
                    fun _ ⟨h1, h2⟩ => Or.inr ⟨by omega, by omega⟩)).mono le_rfl fun _ t₂
                    ⟨hmod_c, htfr₂, hwf₂, hvals₂⟩ => ?_)
              have ht2_t1 {a} (ha : a < selBase + 4 * selLen) : t₂.mem a = t₁.mem a :=
                hmod_c.mem_eq_of_not_mem (by dsimp only [t₁]; rw [htfr]; omega)
                  (by simp only [Set.mem_Ico]; omega)
              have ht2_s {a} (ha : a < selBase + 4 * selLen) (hne : a ≠ usedBase + idx) :
                  t₂.mem a = t.mem a :=
                (ht2_t1 ha).trans (Function.update_of_ne hne _ _)
              have hnd' : (selIdxs ++ [idxFin]).Nodup := List.nodup_append.mpr
                ⟨hnd, List.nodup_singleton _, fun _ ha _ hb hab => by
                  rcases List.mem_singleton.mp hb
                  have := (hused_iff idxFin).mp (hab ▸ ha); dsimp only [idxFin, idx] at this; omega⟩
              refine Memory.FramedTriple.pure ⟨rfl, by dsimp only; omega, by omega,
                htfr₂.trans htfr, hwf₂, fun j hj => by
                  by_cases hji : j = idx
                  · rw [hji, ht2_t1 (by omega)]; dsimp only [t₁]
                    rw [Function.update_self]; exact .inr rfl
                  · rw [ht2_s (by omega) (by omega)]; exact hrange j hj,
                fun a ha => (ht2_s (by omega) (by omega)).trans (hbelow a ha),
                selIdxs ++ [idxFin], by simp only [List.length_append, List.length_singleton,
                  hsl_len], hnd', fun i hi q hq => by
                  rw [List.length_append, List.length_singleton, hsl_len] at hi
                  by_cases hil : i < selLen
                  · rw [List.getElem_append_left (hsl_len ▸ hil), ht2_s (by omega) (by omega)]
                    exact hsel_vals i (hsl_len ▸ hil) q hq
                  · obtain rfl : i = selLen := by omega
                    rw [List.getElem_append_right hsl_len.le]
                    simp only [hsl_len, Nat.sub_self, List.getElem_singleton]
                    exact (hvals₂ q hq).trans ((Function.update_of_ne (by omega) _ _).trans
                      (hbelow _ (by omega))),
                fun id' => by
                  rw [List.mem_append, List.mem_singleton]
                  by_cases hji : id'.val = idx
                  · have : id' = idxFin := Fin.ext hji
                    subst this; rw [ht2_t1 (by omega)]; dsimp only [t₁]
                    rw [Function.update_self]; exact ⟨fun _ => rfl, fun _ => .inr rfl⟩
                  · rw [ht2_s (by omega) (by omega)]
                    exact ⟨fun h => (hused_iff id').mp (h.resolve_right (Fin.ext_iff.not.mpr hji)),
                      fun h => .inl ((hused_iff id').mpr h)⟩,
                fun id' hid' => (List.mem_append.mp hid').elim
                  (fun h1 => let ⟨x, hx, hmx⟩ := hsrc id' h1; ⟨x, by omega, hmx⟩)
                  fun h2 => by rcases List.mem_singleton.mp h2; exact ⟨k, Nat.lt_succ_self k, rfl⟩,
                fun x hx hlt => by
                  by_cases hxk : x = k
                  · rcases hxk with rfl
                    exact List.mem_append.mpr (.inr (List.mem_singleton.mpr (Fin.ext rfl)))
                  · exact List.mem_append.mpr (.inl (hcov x (by omega) hlt))⟩
            · have hflag0' : ¬ t.mem (usedBase + s.mem (minIdxBase + k)) = 0 := hflag0; split_ifs
              exact (Memory.FramedTriple.pure (c := 0) (hkeep_inv fun hlt =>
                (hused_iff ⟨idx, hlt⟩).mpr ((hrange idx hlt_m).resolve_left hflag0))).mono
                (by decide) fun _ _ h => h
          · have hlt_m' : ¬ s.mem (minIdxBase + k) < m := hlt_m; split_ifs
            exact (Memory.FramedTriple.pure (c := 0) (hkeep_inv fun hlt =>
              absurd hlt hlt_m)).mono (by decide) fun _ _ h => h
        obtain ⟨hvh, hcost, hmod, hinv'⟩ := framedTriple_iff_realization.mp hft
        exact ⟨hsafe, hvh, hcost, hmod, hinv'⟩)
      ⟨0, 0⟩ s ⟨rfl, Nat.zero_le 0, Nat.zero_le n, rfl, hwf, fun j hj => .inl (hused_init j hj),
        fun _ _ => rfl, [], rfl, List.nodup_nil, fun _ hi => absurd hi (Nat.not_lt_zero _),
        fun idx => ⟨fun h => (by cases h), fun h => by
          have := hused_init idx.val idx.isLt; omega⟩,
        fun _ h => (by cases h), fun _ h0 => absurd h0 (Nat.not_lt_zero _)⟩
  exact ⟨hsafe, framedTriple_iff_realization.mpr ⟨hvh, by
    simpa only [Nat.add_zero, Nat.zero_add] using hcost,
    hmod, hvert, hle, hfr, hwf', selIdxs, hsl_len, hnd, hvals, hsrc, hcov⟩⟩

/-- Allocates and materializes deduplicated Borůvka-selected edges in `O(m + n)` time. -/
def boruvkaSelectProg (a : BoruvkaSelectArgs) : Memory.Prog BoruvkaSelectResult := do
  let usedBlk ← Memory.allocBlock a.numEdges
  let selBlk ← Memory.allocBlockDirty (4 * a.numVertices)
  let res ← iterate boruvkaCollectStep
    ⟨a.edgeBase, a.minIdxBase, usedBlk.base, selBlk.base, a.numEdges⟩ a.numVertices ⟨0, 0⟩
  pure ⟨selBlk.base, res.selLen⟩

private theorem boruvkaSelectProg_word_spec {w n m edgeBase minIdxBase : ℕ} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin_lt : edgeBase + 4 * m ≤ s.frontier) (hmin_lt : minIdxBase + n ≤ s.frontier)
    (hfit : Fits w (s.frontier + (m + 4 * n + 1))) :
    let usedBase := s.frontier
    let selBase := usedBase + m
    let s₂ : Memory.State := ⟨clear s.mem usedBase m, selBase + 4 * n⟩
    iterationSafe boruvkaCollectStep boruvkaCollectStepSafe w
      ⟨edgeBase, minIdxBase, usedBase, selBase, m⟩ n ⟨0, 0⟩ s₂ ∧
    Memory.FramedTriple w s (boruvkaSelectProg ⟨n, m, edgeBase, minIdxBase⟩) (m + 11 * n + 2) ∅
      fun res s' =>
        res.selBase = s.frontier + m ∧ res.selCount ≤ n ∧ res.selCount ≤ m ∧
        s'.frontier = s.frontier + m + 4 * n ∧ Memory.WellFormed w s' ∧
        ∃ selIdxs : List (Fin m), selIdxs.length = res.selCount ∧ selIdxs.Nodup ∧
          (∀ i (hi : i < selIdxs.length), ∀ q < 4,
            s'.mem (res.selBase + 4 * i + q) = s.mem (edgeBase + 4 * selIdxs[i].val + q)) ∧
          (∀ idx ∈ selIdxs, ∃ x < n, s.mem (minIdxBase + x) = idx.val) ∧
          ∀ x < n, ∀ hlt : s.mem (minIdxBase + x) < m,
            (⟨s.mem (minIdxBase + x), hlt⟩ : Fin m) ∈ selIdxs := by
  let usedBase := s.frontier
  let s₁ : Memory.State := ⟨clear s.mem usedBase m, usedBase + m⟩
  let selBase := usedBase + m
  let s₂ : Memory.State := ⟨s₁.mem, selBase + 4 * n⟩
  have hfit_s1 : Fits w (usedBase + m) := hfit.of_le (by dsimp only [usedBase]; omega)
  have hfit_s2 : Fits w (selBase + 4 * n) := hfit.of_le (by dsimp only [selBase, usedBase]; omega)
  have hs1_lt : ∀ a < s.frontier, s₁.mem a = s.mem a := fun a ha => by
    simp only [s₁]
    exact clear_of_not_owns (by simp only [Block.Owns]; dsimp only [usedBase]; omega)
  have hwf₁ : Memory.WellFormed w s₁ := ⟨hfit_s1, fun a => by
    simp only [s₁, clear]; split_ifs
    · exact fits_zero w
    · exact hwf.mem_fits a⟩
  have hs2_fr : s₂.frontier = s.frontier + m + 4 * n := rfl
  have hcol := boruvkaCollect_iter_word_spec (n := n) (m := m) (edgeBase := edgeBase)
    (minIdxBase := minIdxBase) (usedBase := usedBase) (selBase := selBase) (s := s₂) h16
    ⟨hfit_s2, hwf₁.mem_fits⟩ (by rw [hs2_fr]; omega) (by rw [hs2_fr]; dsimp only [usedBase]; omega)
    hin_lt (by dsimp only [usedBase]; omega)
    (fun j hj => clear_of_owns (by simp only [Block.Owns]; omega)) (le_refl _) (le_refl _)
    (by dsimp only [selBase, usedBase]; omega) (hfit.of_le (by omega))
    (fits_edges_succ h16 hin_lt hfit)
  refine ⟨hcol.1, ((Memory.FramedTriple.allocBlock_bind hfit_s1
    (Memory.FramedTriple.allocBlockDirty_bind hfit_s2 (Memory.FramedTriple.bind_same (c₂ := 0)
      (hcol.2.mono le_rfl fun _ _ ⟨_, hlen_le, hfr', hwf', selIdxs, hsl_len, hnd, hvals, hsrc,
          hcov⟩ => Memory.FramedTriple.pure ⟨rfl, hlen_le, by
        have := (List.subperm_of_subset hnd fun i _ => List.mem_finRange i).length_le
        rw [← hsl_len]; simpa only [List.length_finRange] using this, by rw [hfr'], hwf', selIdxs,
        hsl_len, hnd, fun i hi q hq => (hvals i hi q hq).trans (hs1_lt _ (by omega)),
        fun idx hidx => let ⟨x, hx, hmx⟩ := hsrc idx hidx
          ⟨x, hx, (hs1_lt _ (by omega)).symm.trans hmx⟩,
        fun x hx hlt => by
          have hlt2 : s₂.mem (minIdxBase + x) < m := by
            change s₁.mem (minIdxBase + x) < m; rw [hs1_lt _ (by omega)]; exact hlt
          simpa only [show (⟨s₂.mem (minIdxBase + x), hlt2⟩ : Fin m) =
            ⟨s.mem (minIdxBase + x), hlt⟩ from Fin.ext (hs1_lt _ (by omega))] using
            hcov x hx hlt2⟩)))).mono (by omega) fun _ _ h => h).frame_empty_of_ge_frontier
    fun _ ha => by
      rcases ha with ⟨h1, _⟩ | ⟨h1, _⟩ <;> dsimp only [usedBase, selBase] at h1 <;> omega⟩

/-- Uniform `Realizes .exact` certificate for `boruvkaSelectProg` with `work = 0`. -/
theorem realizes_boruvkaSelectProg : Realizes .exact
    boruvkaSelectProg WordEncoding.encode WordEncoding.encode
    (fun w a s => Fits w 16 ∧ a.edgeBase + 4 * a.numEdges ≤ s.frontier ∧
      a.minIdxBase + a.numVertices ≤ s.frontier ∧
      Fits w (s.frontier + (a.numEdges + 4 * a.numVertices + 1)))
    (fun _ _ => 0) := by
  have hraw : Realizes .exact boruvkaSelectProg WordEncoding.encode WordEncoding.encode
      (fun w a s =>
        let usedBlk := (Memory.spec 0).clientResult s (Memory.allocBlock a.numEdges)
        let s₁ := (Memory.spec 0).clientState s (Memory.allocBlock a.numEdges)
        let selBlk := (Memory.spec 0).clientResult s₁ (Memory.allocBlockDirty (4 * a.numVertices))
        let s₂ := (Memory.spec 0).clientState s₁ (Memory.allocBlockDirty (4 * a.numVertices))
        Fits w 4 ∧ Fits w (4 * a.numVertices) ∧
        iterationSafe boruvkaCollectStep boruvkaCollectStepSafe w
          ⟨a.edgeBase, a.minIdxBase, usedBlk.base, selBlk.base, a.numEdges⟩
          a.numVertices ⟨0, 0⟩ s₂) (fun _ _ => 0) := by
    unfold boruvkaSelectProg
    realize [realizes_allocBlock, realizes_allocBlockDirty, realizes_boruvkaCollectStep]
    · exact h.2.1
    · exact h.1
    · exact iterationSafe_imp h.2.2 (fun _ => rfl) (fun _ _ hs => hs)
  refine hraw.consequence (fun w a s _ hmem ⟨h16, hin_lt, hmin_lt, hfit⟩ => ?_)
    (fun _ _ => le_rfl)
  have h1 : (Memory.spec 0).runClient s (Memory.allocBlock a.numEdges) =
      (⟨s.frontier, a.numEdges⟩, ⟨clear s.mem s.frontier a.numEdges, s.frontier + a.numEdges⟩,
        [.alloc a.numEdges]) := by
    simpa only [bind_pure, StateTransitionSpec.runClient_pure'] using
      Memory.runClient_allocBlock_bind a.numEdges pure s
  have h2 : (Memory.spec 0).runClient ⟨clear s.mem s.frontier a.numEdges, s.frontier + a.numEdges⟩
      (Memory.allocBlockDirty (4 * a.numVertices)) =
      (⟨s.frontier + a.numEdges, 4 * a.numVertices⟩,
        ⟨clear s.mem s.frontier a.numEdges, s.frontier + a.numEdges + 4 * a.numVertices⟩,
        [.allocDirty (4 * a.numVertices)]) := by
    simpa only [bind_pure, StateTransitionSpec.runClient_pure'] using
      Memory.runClient_allocBlockDirty_bind (4 * a.numVertices) pure _
  dsimp only [StateTransitionSpec.clientResult, StateTransitionSpec.clientState]
  rw [h1]
  dsimp only
  rw [h2]
  exact ⟨h16.of_le (by omega), hfit.of_le (by omega),
    (boruvkaSelectProg_word_spec h16 hmem hin_lt hmin_lt hfit).1⟩

/-- Framed specification for `boruvkaSelectProg`: collects unique incident edges from
`minIdxBase` into a newly allocated `res.selBase` array, leaving all cells below `s.frontier`
untouched, in at most `es.length + 11 * n + 2` memory operations. -/
theorem boruvkaSelectProg_spec {w n edgeBase minIdxBase : ℕ} {es : List (IndexedEdge n)}
    {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hin_lt : edgeBase + 4 * es.length ≤ s.frontier)
    (hmin_lt : minIdxBase + n ≤ s.frontier)
    (hfit : Fits w (s.frontier + (es.length + 4 * n + 1))) :
    Memory.FramedTriple w s (boruvkaSelectProg ⟨n, es.length, edgeBase, minIdxBase⟩)
      (es.length + 11 * n + 2) ∅ fun res s' =>
        res.selBase = s.frontier + es.length ∧
        res.selCount ≤ n ∧
        res.selCount ≤ es.length ∧
        s'.frontier = s.frontier + es.length + 4 * n ∧
        Memory.WellFormed w s' ∧
        ∃ selIdxs : List (Fin es.length),
          selIdxs.length = res.selCount ∧
          selIdxs.Nodup ∧
          HoldsIndexedEdges res.selBase (selIdxs.map fun i => es[i.val]) s'.mem ∧
          (∀ idx ∈ selIdxs, ∃ x : Fin n, s.mem (minIdxBase + x.val) = idx.val) ∧
          ∀ x : Fin n, ∀ hlt : s.mem (minIdxBase + x.val) < es.length,
            (⟨s.mem (minIdxBase + x.val), hlt⟩ : Fin es.length) ∈ selIdxs := by
  refine (boruvkaSelectProg_word_spec h16 hwf hin_lt hmin_lt hfit).2.mono le_rfl fun res s'
      ⟨hsb, hcn, hcm, hfr, hwf', selIdxs, hsl_len, hnd, hvals, hsrc, hcov⟩ =>
    ⟨hsb, hcn, hcm, hfr, hwf', selIdxs, hsl_len, hnd, fun i hi => by
      have hi' : i < selIdxs.length := by simpa only [List.length_map] using hi
      obtain ⟨hu, hv, hw, hid⟩ := hin selIdxs[i].val selIdxs[i].isLt
      simp only [List.getElem_map]
      exact ⟨(hvals i hi' 0 (by decide)).trans hu, (hvals i hi' 1 (by decide)).trans hv,
        (hvals i hi' 2 (by decide)).trans hw, (hvals i hi' 3 (by decide)).trans hid⟩,
    fun idx hidx => let ⟨x, hx, hmx⟩ := hsrc idx hidx; ⟨⟨x, hx⟩, hmx⟩,
    fun x hlt => hcov x.val x.isLt hlt⟩

/-! ## Algebraic Helpers & Two-Phase Borůvka Contraction -/

private theorem boruvka_selected_extends_msf {n : ℕ} {es : List (IndexedEdge n)}
    {selIdxs : List (Fin es.length)} (hnd : selIdxs.Nodup)
    (hmin : ∀ idx ∈ selIdxs, ∃ x : Fin n,
      (es[idx.val]).u ≠ (es[idx.val]).v ∧ ((es[idx.val]).u = x ∨ (es[idx.val]).v = x) ∧
      ∀ j : Fin es.length, (es[j.val]).u ≠ (es[j.val]).v →
        ((es[j.val]).u = x ∨ (es[j.val]).v = x) →
        (es[idx.val]).weight < (es[j.val]).weight ∨
          ((es[idx.val]).weight = (es[j.val]).weight ∧ idx.val ≤ j.val)) :
    ∃ F_ext : List (WeightedEdge n ℕ),
      IsMinSpanningForest (es.map IndexedEdge.toWeighted)
        ((selIdxs.map fun i => es[i.val]).map IndexedEdge.toWeighted ++ F_ext) := by
  classical
  let esW := es.map IndexedEdge.toWeighted
  let ends := edgeEnds esW; let wt := edgeWeight esW
  let M := Cslib.Multigraph.msf ends wt Finset.univ
  let idxW : List (Fin esW.length) :=
    selIdxs.map fun i => ⟨i.val, by simp only [esW, List.length_map]; exact i.isLt⟩
  have hsub_W : ∀ i' ∈ idxW, i' ∈ M.toList := fun i' hi' => Finset.mem_toList.mpr <| by
    obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hi'
    obtain ⟨x, hne, hinc, hbest⟩ := hmin idx hidx
    refine Cslib.Multigraph.mem_msf_of_mem_edgeCut wt (P := ({x} : Set (Fin n)))
      (Finset.mem_univ _) (Graph.mem_edgeCut_iff.mpr <| by
        rcases hinc with h1 | h2
        · refine ⟨x, (es[idx.val]).v, ?_, rfl, fun heq => hne (h1.trans heq.symm)⟩
          change edgeEnds (es.map IndexedEdge.toWeighted) ⟨idx.val, _⟩ = _
          simp only [edgeEnds, List.getElem_map, IndexedEdge.toWeighted, h1]
        · refine ⟨x, (es[idx.val]).u, ?_, rfl, fun heq => hne (heq.trans h2.symm)⟩
          change edgeEnds (es.map IndexedEdge.toWeighted) ⟨idx.val, _⟩ = _
          simp only [edgeEnds, List.getElem_map, IndexedEdge.toWeighted, h2, Sym2.eq_swap])
      fun f _ hfcut => by
        obtain ⟨a, b, hab, ha, hb⟩ := Graph.mem_edgeCut_iff.1 hfcut
        simp only [Set.mem_singleton_iff] at ha hb; subst a
        let jf : Fin es.length := ⟨f.val, by simpa only [esW, List.length_map] using f.isLt⟩
        have hbest_f (hne_f : es[jf.val].u ≠ es[jf.val].v)
            (hinc_f : es[jf.val].u = x ∨ es[jf.val].v = x) :
            wt ⟨idx.val, by simp only [esW, List.length_map]; exact idx.isLt⟩ ≤ wt f :=
          (hbest jf hne_f hinc_f).elim
            (fun h => (Prod.Lex.toLex_lt_toLex.mpr (.inl (by
              simpa only [esW, List.getElem_map, IndexedEdge.toWeighted] using h))).le)
            fun ⟨h1, h2⟩ => Prod.Lex.toLex_le_toLex.mpr (.inr ⟨by
              simpa only [esW, List.getElem_map, IndexedEdge.toWeighted] using h1, h2⟩)
        change edgeEnds (es.map IndexedEdge.toWeighted) f = s(x, b) at hab
        simp only [edgeEnds, List.getElem_map, IndexedEdge.toWeighted] at hab
        change s((es[jf.val]).u, (es[jf.val]).v) = s(x, b) at hab
        rcases Sym2.eq_iff.mp hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hbest_f (fun heq => hb (h1.symm.trans (heq.trans h2)).symm) (.inl h1)
        · exact hbest_f (fun heq => hb (h2.symm.trans (heq.symm.trans h1)).symm) (.inr h2)
  have hm : ((selIdxs.map fun i => es[i.val]).map IndexedEdge.toWeighted).Subperm
      (msfEdges esW wt) := by
    rw [show (selIdxs.map fun i => es[i.val]).map IndexedEdge.toWeighted =
        idxW.map (fun i : Fin esW.length => esW[i.val]) from by
      simp only [idxW, esW, List.map_map, Function.comp_def, List.getElem_map]]
    exact List.subperm_map (fun i : Fin esW.length => esW[i.val]) (List.subperm_of_subset
      (show idxW.Nodup from
        hnd.map fun _ _ h => Fin.ext (congrArg (Fin.val : Fin esW.length → ℕ) h)) hsub_W)
  exact exists_extend_isMinSpanningForest_of_subperm_msfEdges esW _ hm

/-- Lifts any MSF `L_out` of the compacted deduplicated graph produced by `boruvkaStepProg` back
to original edges `L_orig` so `selEs ++ L_orig` is an MSF of `es`. -/
theorem boruvkaStepProg_lift_msf {n nComp nOut : ℕ}
    {es selEs : List (IndexedEdge n)}
    {compFn : Fin n → Fin nComp}
    {esCon esDedup : List (IndexedEdge nComp)}
    {lift : Fin nOut → Fin nComp}
    {esOut : List (IndexedEdge nOut)}
    (hsel_sub : selEs.Subperm es)
    (hsel_ext : ∃ F_ext : List (WeightedEdge n ℕ),
      IsMinSpanningForest (es.map IndexedEdge.toWeighted)
        (selEs.map IndexedEdge.toWeighted ++ F_ext))
    (hcomp_surj : Function.Surjective compFn)
    (hcomp_rel : ∀ x y : Fin n, compFn x = compFn y ↔
      (edgePartition (selEs.map IndexedEdge.toWeighted)).rel x y = true)
    (hes_con : es.map (fun e => ⟨compFn e.u, compFn e.v, e.weight, e.id⟩) = esCon)
    (hdedup_sub : esDedup.Subperm esCon)
    (hdedup_eq : esDedup.map IndexedEdge.toWeighted =
      dedupSimpleEdges (esCon.map IndexedEdge.toWeighted))
    (hdedup_simp : IsSimple (edgeEnds (esDedup.map IndexedEdge.toWeighted)))
    (hlift_inj : Function.Injective lift)
    (hes_compact : esOut.map (fun e => ⟨lift e.u, lift e.v, e.weight, e.id⟩) = esDedup)
    {L_out : List (IndexedEdge nOut)}
    (hL_sub : L_out.Subperm esOut)
    (hL_msf : IsMinSpanningForest (esOut.map IndexedEdge.toWeighted)
      (L_out.map IndexedEdge.toWeighted)) :
    ∃ L_orig : List (IndexedEdge n),
      (selEs ++ L_orig).Subperm es ∧
      L_orig.map IndexedEdge.id = L_out.map IndexedEdge.id ∧
      IsMinSpanningForest (es.map IndexedEdge.toWeighted)
        ((selEs ++ L_orig).map IndexedEdge.toWeighted) := by
  let remapper (e : IndexedEdge n) : IndexedEdge nComp :=
    ⟨compFn e.u, compFn e.v, e.weight, e.id⟩
  let clift (e : IndexedEdge nOut) : IndexedEdge nComp := ⟨lift e.u, lift e.v, e.weight, e.id⟩
  have hL_dedup_sub : (L_out.map clift).Subperm esDedup :=
    hes_compact ▸ List.subperm_map clift hL_sub
  obtain ⟨L_orig, hL_orig_sub, hL_orig_map⟩ :=
    (hL_dedup_sub.trans hdedup_sub |>.trans (by rw [← hes_con])).exists_map
  have hdisj : List.Disjoint selEs L_orig := List.disjoint_left.mpr fun e he_sel he_L => by
    obtain ⟨i, hi, hi_eq⟩ := List.mem_iff_getElem.mp (hL_dedup_sub.subset
      (hL_orig_map ▸ List.mem_map.mpr ⟨e, he_L, rfl⟩))
    have hno := ((isSimple_iff _).mp hdedup_simp).1 ⟨i, by simp only [List.length_map]; exact hi⟩
    simp only [edgeEnds, List.getElem_map, IndexedEdge.toWeighted] at hno
    rw [hi_eq, Sym2.mk_isDiag_iff] at hno
    exact hno ((hcomp_rel e.u e.v).mpr ((rel_edgePartition_iff_eqvGen _ _ _).mpr
      (.rel _ _ ⟨e.toWeighted, List.mem_map.mpr ⟨e, he_sel, rfl⟩, rfl, rfl⟩)))
  have hL_con_msf : IsMinSpanningForest (contractEdgeList compFn (es.map IndexedEdge.toWeighted))
      (contractEdgeList compFn (L_orig.map IndexedEdge.toWeighted)) := by
    rw [show contractEdgeList compFn (es.map IndexedEdge.toWeighted) =
        esCon.map IndexedEdge.toWeighted from by
      rw [← hes_con]; simp only [contractEdgeList, List.map_map, Function.comp_def, contractEdge,
        IndexedEdge.toWeighted],
      show contractEdgeList compFn (L_orig.map IndexedEdge.toWeighted) =
        (L_out.map clift).map IndexedEdge.toWeighted from by
      rw [← hL_orig_map]; simp only [contractEdgeList, List.map_map, Function.comp_def,
        contractEdge, IndexedEdge.toWeighted]]
    refine isMinSpanningForest_of_dedupSimpleEdges _ _ (hdedup_eq ▸ ?_)
    simpa only [clift, contractEdgeList, List.map_map, Function.comp_def, contractEdge,
      IndexedEdge.toWeighted] using compactVertices_isMinSpanningForest hlift_inj
        hes_compact hL_msf
  obtain ⟨F_ext, hmsf_ext⟩ := hsel_ext
  refine ⟨L_orig, hsel_sub.append_of_disjoint hL_orig_sub hdisj, by
    simpa only [remapper, clift, List.map_map, Function.comp_def] using
      congrArg (List.map IndexedEdge.id) hL_orig_map, ?_⟩
  simpa only [List.map_append] using isMinSpanningForest_append_of_contract
    (es.map IndexedEdge.toWeighted) (selEs.map IndexedEdge.toWeighted)
    (L_orig.map IndexedEdge.toWeighted) compFn (List.subperm_map IndexedEdge.toWeighted hsel_sub)
    (isAcyclic_sublist (List.sublist_append_left _ _) hmsf_ext.1.2.1) hcomp_rel hcomp_surj
    ⟨F_ext, hmsf_ext⟩ (List.subperm_map IndexedEdge.toWeighted hL_orig_sub) hL_con_msf

/-- Phase 1 of Borůvka contraction: computes minimum incident edges, materializes `sel`, and runs
BFS connected components in `O(m + n)` time. -/
def boruvkaPartitionProg (g : GraphSlice) : Memory.Prog BoruvkaPartitionResult := do
  let minIdxBase ← boruvkaMinProg g
  let sel ← boruvkaSelectProg ⟨g.numVertices, g.numEdges, g.edgeBase, minIdxBase⟩
  let cc ← connectedComponentsProg ⟨g.numVertices, sel.selCount, sel.selBase⟩
  pure ⟨sel.selBase, sel.selCount, cc.compBase, cc.numComps⟩

/-- Framed specification for `boruvkaPartitionProg`: selects lightest incident edges and computes
component labels induced by those edges, leaving all cells below `s.frontier` untouched, in at
most `10 * es.length + 50 * n + 11` memory operations. -/
theorem boruvkaPartitionProg_spec {w n edgeBase : ℕ} {es : List (IndexedEdge n)}
    {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hin_lt : edgeBase + 4 * es.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + (es.length + 13 * n + 1))) :
    Memory.FramedTriple w s (boruvkaPartitionProg ⟨n, es.length, edgeBase⟩)
      (10 * es.length + 50 * n + 11) ∅ fun res s' =>
        s'.frontier ≤ s.frontier + (es.length + 13 * n + 1) ∧
        s.frontier ≤ res.selBase ∧
        res.selBase + 4 * res.selCount ≤ s'.frontier ∧
        s.frontier ≤ res.compBase ∧
        res.compBase + n ≤ s'.frontier ∧
        res.selCount ≤ n ∧ res.selCount ≤ es.length ∧ res.numComps ≤ n ∧
        Memory.WellFormed w s' ∧
        ∃ (selIdxs : List (Fin es.length)) (compFn : Fin n → Fin res.numComps),
          selIdxs.length = res.selCount ∧
          selIdxs.Nodup ∧
          (selIdxs.map fun i => es[i.val]).Subperm es ∧
          (∃ F_ext : List (WeightedEdge n ℕ),
            IsMinSpanningForest (es.map IndexedEdge.toWeighted)
              ((selIdxs.map fun i => es[i.val]).map IndexedEdge.toWeighted ++ F_ext)) ∧
          HoldsIndexedEdges res.selBase (selIdxs.map fun i => es[i.val]) s'.mem ∧
          (∀ x : Fin n, (∃ e ∈ es, e.u ≠ e.v ∧ (e.u = x ∨ e.v = x)) →
            ∃ idx ∈ selIdxs, (es[idx.val]).u ≠ (es[idx.val]).v ∧
              ((es[idx.val]).u = x ∨ (es[idx.val]).v = x)) ∧
          (∀ u : Fin n, s'.mem (res.compBase + u.val) = (compFn u).val) ∧
          Function.Surjective compFn ∧
          (∀ x y : Fin n, compFn x = compFn y ↔
            (edgePartition ((selIdxs.map fun i => es[i.val]).map IndexedEdge.toWeighted)).rel x y =
              true) ∧
          (∀ idx ∈ selIdxs, ∃ x : Fin n, IsVertexMinEdge es x idx) ∧
          ∀ x : Fin n, (∃ e ∈ es, e.u ≠ e.v ∧ (e.u = x ∨ e.v = x)) →
            ∃ idx ∈ selIdxs, IsVertexMinEdge es x idx := by
  dsimp only [boruvkaPartitionProg]
  refine (Memory.FramedTriple.bind_same (c₂ := (es.length + 11 * n + 2) + (24 * n + 13 * n + 8))
    ((holdsIndexedEdges_frame_mem (boruvkaMinProg_spec h16 hwf hin hin_lt (hfit.of_le (by omega)))
      hin (Set.empty_disjoint _) hin_lt).mono le_rfl
        fun minIdxBase s₁ ⟨⟨hmin_res, hfr₁, hwf₁, hopt⟩, hin₁⟩ => ?_)).mono (by omega)
        fun _ _ h => h
  have hsel := boruvkaSelectProg_spec (minIdxBase := minIdxBase) h16 hwf₁ hin₁ (by rw [hfr₁]; omega)
    (by rw [hmin_res, hfr₁]) (hfit.of_le (by rw [hfr₁]; omega))
  refine (Memory.FramedTriple.bind_same (c₂ := 24 * n + 13 * n + 8)
    (hsel.mono le_rfl fun sel s₂ ⟨hsel_b, hsel_cn, hsel_cm, hfr₂, hwf₂, selIdxs, hsl_len, hnd,
      hsel_holds, hsrc, hcov⟩ => ?_)).mono (by omega) fun _ _ h => h
  let selEs := selIdxs.map fun i => es[i.val]
  have hsel_len_eq : selEs.length = sel.selCount := by simp only [selEs, List.length_map, hsl_len]
  have hcc := holdsIndexedEdges_frame_mem (@connectedComponentsProg_spec w n sel.selBase selEs s₂
    h16 hwf₂ hsel_holds (by rw [hsel_len_eq, hsel_b, hfr₂]; omega)
    (hfit.of_le (by rw [hsel_len_eq, hfr₂, hfr₁]; omega))) hsel_holds (Set.empty_disjoint _)
    (by rw [hsel_len_eq, hsel_b, hfr₂]; have := hsel_cn; omega)
  rw [hsel_len_eq] at hcc
  refine (Memory.FramedTriple.bind_same (c₂ := 0) (hcc.mono le_rfl fun cc s₃
      ⟨⟨hcc_b, hcc_le, hfr₃, hwf₃, hcc_lt, hcc_surj, hcc_rel, _⟩, hsel_holds3⟩ => ?_)).mono
    (by omega) fun _ _ h => h
  have hsel_sub : selEs.Subperm es := by
    simpa only [List.map_getElem_finRange] using List.subperm_map
      (fun i : Fin es.length => es[i.val])
      (List.subperm_of_subset hnd fun i _ => List.mem_finRange i)
  have hmin_at (x : Fin n) (idx : Fin es.length)
      (hmx : s₁.mem (minIdxBase + x.val) = idx.val) : IsVertexMinEdge es x idx := by
    rcases hopt x with ⟨heq, _⟩ | ⟨idx', heq, hne, hinc, hbest⟩
    · exact absurd hmx.symm (by rw [heq]; exact Nat.ne_of_lt idx.isLt)
    · exact (Fin.ext (hmx.symm.trans heq)) ▸ ⟨hne, hinc, hbest⟩
  have hsel_sound : ∀ idx ∈ selIdxs, ∃ x : Fin n, IsVertexMinEdge es x idx :=
    fun idx hidx => let ⟨x, hx⟩ := hsrc idx hidx; ⟨x, hmin_at x idx hx⟩
  have hsel_msf := boruvka_selected_extends_msf hnd hsel_sound
  have hcov_min : ∀ x : Fin n, (∃ e ∈ es, e.u ≠ e.v ∧ (e.u = x ∨ e.v = x)) →
      ∃ idx ∈ selIdxs, IsVertexMinEdge es x idx := by
    rintro x ⟨e, he_es, hne_e, hinc_e⟩
    obtain ⟨i_e, hi_e, rfl⟩ := List.mem_iff_getElem.mp he_es
    rcases hopt x with ⟨_, hnone⟩ | ⟨idx, heq, hne_idx, hinc_idx, hbest⟩
    · exact absurd hinc_e (not_or.mpr (hnone ⟨i_e, hi_e⟩ hne_e))
    · have hlt : s₁.mem (minIdxBase + x.val) < es.length := heq ▸ idx.isLt
      exact ⟨idx, (show (⟨s₁.mem (minIdxBase + x.val), hlt⟩ : Fin es.length) = idx from
        Fin.ext heq) ▸ hcov x hlt, hne_idx, hinc_idx, hbest⟩
  have hcov_nonloop : ∀ x : Fin n, (∃ e ∈ es, e.u ≠ e.v ∧ (e.u = x ∨ e.v = x)) →
      ∃ idx ∈ selIdxs, (es[idx.val]).u ≠ (es[idx.val]).v ∧
        ((es[idx.val]).u = x ∨ (es[idx.val]).v = x) :=
    fun x hx => let ⟨idx, hmem, hne, hinc, _⟩ := hcov_min x hx; ⟨idx, hmem, hne, hinc⟩
  exact Memory.FramedTriple.pure ⟨by rw [hfr₃, hfr₂, hfr₁]; omega,
    by dsimp only; rw [hsel_b, hfr₁]; omega, by dsimp only; rw [hfr₃, hfr₂, hsel_b]; omega,
    by dsimp only; rw [hcc_b, hfr₂, hfr₁]; omega, by dsimp only; rw [hfr₃, hcc_b]; omega,
    hsel_cn, hsel_cm, hcc_le, hwf₃, selIdxs, fun u => ⟨s₃.mem (cc.compBase + u.val), hcc_lt u⟩,
    hsl_len, hnd, hsel_sub, hsel_msf, hsel_holds3, hcov_nonloop, fun _ => rfl,
    fun c => let ⟨u, hu⟩ := hcc_surj c; ⟨u, Fin.ext hu⟩, fun x y => Fin.ext_iff.trans (hcc_rel x y),
    hsel_sound, hcov_min⟩

private theorem boruvkaPartition_word_posts {w : ℕ} {d : GraphSlice} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (h16 : Fits w 16)
    (hin_lt : d.edgeBase + 4 * d.numEdges ≤ s.frontier)
    (hfit : Fits w (s.frontier + (d.numEdges + 13 * d.numVertices + 1)))
    (hedges : ∀ j < d.numEdges, s.mem (d.edgeBase + 4 * j) < d.numVertices ∧
      s.mem (d.edgeBase + 4 * j + 1) < d.numVertices) :
    let mb := (Memory.spec 0).clientResult s (boruvkaMinProg d)
    let s₁ := (Memory.spec 0).clientState s (boruvkaMinProg d)
    let sel := (Memory.spec 0).clientResult s₁
      (boruvkaSelectProg ⟨d.numVertices, d.numEdges, d.edgeBase, mb⟩)
    let s₂ := (Memory.spec 0).clientState s₁
      (boruvkaSelectProg ⟨d.numVertices, d.numEdges, d.edgeBase, mb⟩)
    (d.edgeBase + 4 * d.numEdges ≤ s₁.frontier ∧ mb + d.numVertices ≤ s₁.frontier ∧
      Fits w (s₁.frontier + (d.numEdges + 4 * d.numVertices + 1))) ∧
    (sel.selBase + 4 * sel.selCount ≤ s₂.frontier ∧
      Fits w (s₂.frontier + (4 * d.numVertices + 4 * sel.selCount + 1)) ∧
      ∀ j < sel.selCount, s₂.mem (sel.selBase + 4 * j) < d.numVertices ∧
        s₂.mem (sel.selBase + 4 * j + 1) < d.numVertices) := by
  rcases d with ⟨n, m, eb⟩; dsimp only at *
  obtain ⟨es, hlen, hin⟩ := exists_indexedEdges_of_mem_lt hedges
  have hmin_ft := holdsIndexedEdges_frame_mem (boruvkaMinProg_spec h16 hwf hin
    (by rw [hlen]; exact hin_lt) (hfit.of_le (by omega))) hin (Set.empty_disjoint _)
    (by rw [hlen]; exact hin_lt)
  rw [show (⟨n, es.length, eb⟩ : GraphSlice) = ⟨n, m, eb⟩ from by rw [hlen]] at hmin_ft
  obtain ⟨_, _, _, ⟨hres₁, hfr₁, hwf₁, _⟩, hin₁⟩ := framedTriple_iff_realization.mp hmin_ft
  have hsel_ft := boruvkaSelectProg_spec
    (minIdxBase := (Memory.spec 0).clientResult s (boruvkaMinProg ⟨n, m, eb⟩)) h16 hwf₁ hin₁
    (by rw [hfr₁, hlen]; omega) (by rw [hres₁, hfr₁])
    (by rw [hfr₁, hlen]; exact hfit.of_le (by omega))
  rw [show (⟨n, es.length, eb, _⟩ : BoruvkaSelectArgs) = ⟨n, m, eb, _⟩ from by rw [hlen]]
    at hsel_ft
  obtain ⟨_, _, _, hsb, hcn, _, hfr₂, _, selIdxs, hsl_len, _, hsel_holds, _⟩ :=
    framedTriple_iff_realization.mp hsel_ft
  refine ⟨⟨by rw [hfr₁]; omega, by rw [hres₁, hfr₁], by rw [hfr₁]; exact hfit.of_le (by omega)⟩,
    ⟨by rw [hfr₂, hsb]; omega, by rw [hfr₂, hfr₁, hlen]; exact hfit.of_le (by omega), fun j hj => by
      obtain ⟨hu, hv, _⟩ := hsel_holds j (by rw [List.length_map, hsl_len]; exact hj)
      simp only [List.getElem_map] at hu hv
      exact ⟨hu ▸ es[selIdxs[j].val].u.isLt, hv ▸ es[selIdxs[j].val].v.isLt⟩⟩⟩

/-- Uniform `Realizes .exact` certificate for `boruvkaPartitionProg` with `work = 0`. -/
theorem realizes_boruvkaPartitionProg : Realizes .exact
    boruvkaPartitionProg WordEncoding.encode WordEncoding.encode
    (fun w g s => Fits w 16 ∧ g.edgeBase + 4 * g.numEdges ≤ s.frontier ∧
      Fits w (s.frontier + (g.numEdges + 13 * g.numVertices + 1)) ∧
      ∀ j < g.numEdges, s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
        s.mem (g.edgeBase + 4 * j + 1) < g.numVertices)
    (fun _ _ => 0) := by
  unfold boruvkaPartitionProg
  realize [realizes_boruvkaMinProg, realizes_boruvkaSelectProg, realizes_connectedComponentsProg]
  all_goals
    obtain ⟨h16, hin_lt, hfit, hedges⟩ := h
    first
    | exact h16 | exact hin_lt | exact hfit.of_le (by omega) | exact hedges
    | (obtain ⟨⟨a1, b1, c1⟩, ⟨a2, b2, c2⟩⟩ :=
         boruvkaPartition_word_posts hmem h16 hin_lt hfit hedges
       first | exact a1 | exact b1 | exact c1 | exact a2 | exact b2 | exact c2)

/-- Phase 2 of Borůvka contraction: remaps edge endpoints along component labels, removes
self-loops and duplicate parallel edges, and compacts isolated vertices in `O(m + nComp)` time. -/
def boruvkaShrinkProg (a : BoruvkaShrinkArgs) : Memory.Prog GraphSlice := do
  let conBase ← contractEdgesProg ⟨a.numEdges, a.edgeBase, a.compBase⟩
  let dedup ← dedupSimpleEdgesProg ⟨a.numComps, a.numEdges, conBase⟩
  let comp ← compactVerticesProg ⟨a.numComps, dedup.numEdges, dedup.edgeBase⟩
  pure ⟨comp.numVertices, dedup.numEdges, comp.edgeBase⟩

/-- Framed specification for `boruvkaShrinkProg`: contracts, deduplicates, and vertex-compacts
in at most `66 * es.length + 11 * nComp + 23` memory operations using at most
`21 * es.length + 3 * nComp + 3` words while leaving cells below `s.frontier` untouched. -/
theorem boruvkaShrinkProg_spec {w n nComp edgeBase compBase : ℕ}
    {es : List (IndexedEdge n)} {compFn : Fin n → Fin nComp} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hin_lt : edgeBase + 4 * es.length ≤ s.frontier)
    (hcomp : ∀ u : Fin n, s.mem (compBase + u.val) = (compFn u).val)
    (hcomp_disj : compBase + n ≤ s.frontier)
    (hfit : Fits w (s.frontier + (21 * es.length + 3 * nComp + 3))) :
    Memory.FramedTriple w s (boruvkaShrinkProg ⟨n, nComp, es.length, edgeBase, compBase⟩)
      (66 * es.length + 11 * nComp + 23) ∅ fun res s' =>
        s'.frontier ≤ s.frontier + (21 * es.length + 3 * nComp + 3) ∧
        s.frontier ≤ res.edgeBase ∧
        res.edgeBase + 4 * res.numEdges ≤ s'.frontier ∧
        res.numVertices ≤ nComp ∧ res.numEdges ≤ es.length ∧
        Memory.WellFormed w s' ∧
        ∃ (esCon esDedup : List (IndexedEdge nComp))
            (lift : Fin res.numVertices → Fin nComp)
            (esOut : List (IndexedEdge res.numVertices)),
          es.map (fun e => ⟨compFn e.u, compFn e.v, e.weight, e.id⟩) = esCon ∧
          esDedup.Subperm esCon ∧
          esDedup.map IndexedEdge.toWeighted =
            dedupSimpleEdges (esCon.map IndexedEdge.toWeighted) ∧
          IsSimple (edgeEnds (esDedup.map IndexedEdge.toWeighted)) ∧
          Function.Injective lift ∧
          esOut.length = res.numEdges ∧
          HoldsIndexedEdges res.edgeBase esOut s'.mem ∧
          (∀ y : Fin res.numVertices, ∃ e ∈ esOut, e.u = y ∨ e.v = y) ∧
          esOut.map (fun e => ⟨lift e.u, lift e.v, e.weight, e.id⟩) = esDedup := by
  dsimp only [boruvkaShrinkProg]
  refine (Memory.FramedTriple.bind_same
    (c₂ := (41 * es.length + 6 * nComp + 6) + (14 * es.length + 3 * nComp + 2))
    ((@contractEdgesProg_spec w n nComp edgeBase compBase es (fun x => (compFn x).val) s h16 hwf
      hin hin_lt hcomp hcomp_disj (fun e _ => ⟨(compFn e.u).isLt, (compFn e.v).isLt⟩)
      (hfit.of_le (by omega))).mono
      le_rfl fun conBase s₁ ⟨hres_con, hfr₁, hwf₁, esCon, hlen_con, hcon_holds, hel_con⟩ =>
        ?_)).mono (by omega) fun _ _ h => h
  have hded := FramedTriple.with_modifies (dedupSimpleEdgesProg_spec h16 hwf₁ hcon_holds
    (by rw [hlen_con, hres_con, hfr₁]) (hfit.of_le (by rw [hlen_con, hfr₁]; omega)))
  rw [show (⟨nComp, esCon.length, conBase⟩ : GraphSlice) = ⟨nComp, es.length, conBase⟩ from by
    rw [hlen_con]] at hded
  refine (Memory.FramedTriple.bind_same (c₂ := 14 * es.length + 3 * nComp + 2)
    (hded.mono le_rfl fun dedup s₂ ⟨hmod₂, _, hded_bound, hfr₂_le, hwf₂, esDedup, hlen_ded,
      hded_sub, hded_holds, hded_eq, hded_simp, _⟩ => ?_)).mono (by rw [hlen_con]) fun _ _ h => h
  have hfr₁_le : s₁.frontier ≤ s₂.frontier := hmod₂.1
  have hfr_s2 : s.frontier ≤ s₂.frontier := by rw [hfr₁] at hfr₁_le; omega
  rw [hfr₁, hlen_con] at hfr₂_le
  have hded_le : dedup.numEdges ≤ es.length := hlen_ded ▸ hded_sub.length_le.trans hlen_con.le
  have hcmp := compactVerticesProg_spec h16 hwf₂ hded_holds
    (by rw [hlen_ded]; exact hded_bound) (hfit.of_le (by rw [hlen_ded]; omega))
  rw [show (⟨nComp, esDedup.length, dedup.edgeBase⟩ : GraphSlice) =
    ⟨nComp, dedup.numEdges, dedup.edgeBase⟩ from by rw [hlen_ded]] at hcmp
  refine (Memory.FramedTriple.bind_same (c₂ := 0) (hcmp.mono le_rfl fun comp s₃
      ⟨_, hcmp_eb, hcmp_nv, hfr₃, hwf₃, lift, esOut, hlift_inj, hlen_out, hout_holds, _,
        hout_cover, hes_compact⟩ => ?_)).mono (by rw [hlen_ded]; omega) fun _ _ h => h
  exact Memory.FramedTriple.pure ⟨by rw [hfr₃, hlen_ded]; omega,
    by dsimp only; rw [hcmp_eb]; omega,
    by dsimp only; rw [hfr₃, hcmp_eb, hlen_ded], hcmp_nv, hded_le, hwf₃, esCon, esDedup, lift,
    esOut, List.ext_getElem (by simp only [List.length_map, hlen_con]) fun i hi₁ hi₂ => by
      obtain ⟨hu, hv, hw, hid⟩ := hel_con i (by simpa only [List.length_map] using hi₁) hi₂
      simp only [List.getElem_map]
      exact congr (congr (congr (congrArg IndexedEdge.mk (Fin.ext hu.symm)) (Fin.ext hv.symm))
        hw.symm) hid.symm,
    hded_sub, hded_eq, hded_simp, hlift_inj, hlen_out.trans hlen_ded, hout_holds,
    hout_cover, hes_compact⟩

private theorem boruvkaShrink_word_posts {w : ℕ} {d : BoruvkaShrinkArgs} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin_lt : d.edgeBase + 4 * d.numEdges ≤ s.frontier)
    (hcomp_disj : d.compBase + d.numVertices ≤ s.frontier)
    (hfit : Fits w (s.frontier + (21 * d.numEdges + 3 * d.numComps + 3)))
    (hedges : ∀ j < d.numEdges, s.mem (d.edgeBase + 4 * j) < d.numVertices ∧
      s.mem (d.edgeBase + 4 * j + 1) < d.numVertices)
    (hcomp : ∀ u < d.numVertices, s.mem (d.compBase + u) < d.numComps) :
    let p₀ : ContractEdgesArgs := ⟨d.numEdges, d.edgeBase, d.compBase⟩
    let cb := (Memory.spec 0).clientResult s (contractEdgesProg p₀)
    let s₁ := (Memory.spec 0).clientState s (contractEdgesProg p₀)
    let g₁ : GraphSlice := ⟨d.numComps, d.numEdges, cb⟩
    let dedup := (Memory.spec 0).clientResult s₁ (dedupSimpleEdgesProg g₁)
    let s₂ := (Memory.spec 0).clientState s₁ (dedupSimpleEdgesProg g₁)
    (cb + 4 * d.numEdges ≤ s₁.frontier ∧ Fits w (s₁.frontier + (13 * d.numEdges + 2 * d.numComps)) ∧
      ∀ j < d.numEdges, s₁.mem (cb + 4 * j) < d.numComps ∧
        s₁.mem (cb + 4 * j + 1) < d.numComps) ∧
    (dedup.edgeBase + 4 * dedup.numEdges ≤ s₂.frontier ∧
      Fits w (s₂.frontier + (d.numComps + 4 * dedup.numEdges + 1)) ∧
      ∀ j < dedup.numEdges, s₂.mem (dedup.edgeBase + 4 * j) < d.numComps ∧
        s₂.mem (dedup.edgeBase + 4 * j + 1) < d.numComps) := by
  rcases d with ⟨n, nComp, m, eb, cb⟩; dsimp only at *
  obtain ⟨es, hlen, hin⟩ := exists_indexedEdges_of_mem_lt hedges
  let compFn : Fin n → Fin nComp := fun u => ⟨s.mem (cb + u.val), hcomp u.val u.isLt⟩
  have hcon_ft := @contractEdgesProg_spec w n nComp eb cb es (fun x => (compFn x).val) s h16 hwf
    hin (by rw [hlen]; exact hin_lt) (fun _ => rfl) hcomp_disj
    (fun e _ => ⟨(compFn e.u).isLt, (compFn e.v).isLt⟩) (by rw [hlen]; exact hfit.of_le (by omega))
  rw [show (⟨es.length, eb, cb⟩ : ContractEdgesArgs) = ⟨m, eb, cb⟩ from by rw [hlen]]
    at hcon_ft
  obtain ⟨_, _, _, hout, hfr₁, hwf₁, esCon, hlen_con, hcon_holds, _⟩ :=
    framedTriple_iff_realization.mp hcon_ft
  have hded_ft := dedupSimpleEdgesProg_spec h16 hwf₁ hcon_holds
    (by rw [hlen_con, hout, hfr₁]) (hfit.of_le (by rw [hlen_con, hfr₁]; omega))
  rw [show (⟨nComp, esCon.length, _⟩ : GraphSlice) = ⟨nComp, m, _⟩ from by rw [hlen_con, hlen]]
    at hded_ft
  obtain ⟨_, _, _, _, hded_bound, hfr₂_le, _, esDedup, hlen_ded, hded_sub, hded_holds, _⟩ :=
    framedTriple_iff_realization.mp hded_ft
  have hded_le : esDedup.length ≤ m := hded_sub.length_le.trans (hlen_con.trans hlen).le
  refine ⟨⟨by rw [hout, hfr₁]; omega, by rw [hfr₁]; exact hfit.of_le (by omega), fun j hj => by
      obtain ⟨hu, hv, _⟩ := hcon_holds j ((hlen_con.trans hlen) ▸ hj)
      exact ⟨hu ▸ esCon[j].u.isLt, hv ▸ esCon[j].v.isLt⟩⟩,
    ⟨hded_bound, hfit.of_le (by rw [hlen_con, hlen, hfr₁] at hfr₂_le; rw [← hlen_ded]; omega),
      fun j hj => by
        obtain ⟨hu, hv, _⟩ := hded_holds j (hlen_ded.symm ▸ hj)
        exact ⟨hu ▸ esDedup[j].u.isLt, hv ▸ esDedup[j].v.isLt⟩⟩⟩

/-- Uniform `Realizes .exact` certificate for `boruvkaShrinkProg` with `work = 0`. -/
theorem realizes_boruvkaShrinkProg : Realizes .exact
    boruvkaShrinkProg WordEncoding.encode WordEncoding.encode
    (fun w a s => Fits w 16 ∧ a.edgeBase + 4 * a.numEdges ≤ s.frontier ∧
      a.compBase + a.numVertices ≤ s.frontier ∧
      Fits w (s.frontier + (21 * a.numEdges + 3 * a.numComps + 3)) ∧
      (∀ j < a.numEdges, s.mem (a.edgeBase + 4 * j) < a.numVertices ∧
        s.mem (a.edgeBase + 4 * j + 1) < a.numVertices) ∧
      ∀ u < a.numVertices, s.mem (a.compBase + u) < a.numComps)
    (fun _ _ => 0) := by
  unfold boruvkaShrinkProg
  realize [realizes_contractEdgesProg, realizes_dedupSimpleEdgesProg, realizes_compactVerticesProg]
  all_goals
    obtain ⟨h16, hin_lt, hcomp_disj, hfit, hedges, hcomp⟩ := h
    have hfront := hmem.frontier_fits
    first
    | exact h16 | exact hfit.of_le (by omega)
    | (intro j hj; exact ⟨by omega, by have := (hedges j hj).1; omega,
         by have := (hedges j hj).2; omega⟩)
    | (obtain ⟨⟨a1, b1, c1⟩, ⟨a2, b2, c2⟩⟩ :=
         boruvkaShrink_word_posts h16 hmem hin_lt hcomp_disj hfit hedges hcomp
       first | exact a1 | exact b1 | exact c1 | exact a2 | exact b2 | exact c2)

/-- Executes one complete Borůvka contraction round on `g`: runs `boruvkaPartitionProg` and
`boruvkaShrinkProg` in `O(m + n)` time. -/
def boruvkaStepProg (g : GraphSlice) : Memory.Prog BoruvkaStepResult := do
  let p ← boruvkaPartitionProg g
  let out ← boruvkaShrinkProg ⟨g.numVertices, p.numComps, g.numEdges, g.edgeBase, p.compBase⟩
  pure ⟨p.selBase, p.selCount, out.numVertices, out.numEdges, out.edgeBase⟩

private theorem boruvkaStep_two_mul_le {n nComp nOut : ℕ}
    {es : List (IndexedEdge n)} {selIdxs : List (Fin es.length)}
    {compFn : Fin n → Fin nComp}
    {esCon esDedup : List (IndexedEdge nComp)}
    {lift : Fin nOut → Fin nComp}
    {esOut : List (IndexedEdge nOut)}
    (hes_con : es.map (fun e => ⟨compFn e.u, compFn e.v, e.weight, e.id⟩) = esCon)
    (hded_sub : esDedup.Subperm esCon)
    (hlift_inj : Function.Injective lift)
    (hout_cover : ∀ y : Fin nOut, ∃ e ∈ esOut, e.u = y ∨ e.v = y)
    (hes_compact : esOut.map (fun e => ⟨lift e.u, lift e.v, e.weight, e.id⟩) = esDedup)
    (hes_out_simp : IsSimple (edgeEnds (esOut.map IndexedEdge.toWeighted)))
    (hcov_nonloop : ∀ x : Fin n, (∃ e ∈ es, e.u ≠ e.v ∧ (e.u = x ∨ e.v = x)) →
      ∃ idx ∈ selIdxs, (es[idx.val]).u ≠ (es[idx.val]).v ∧
        ((es[idx.val]).u = x ∨ (es[idx.val]).v = x))
    (hcomp_rel : ∀ x y : Fin n, compFn x = compFn y ↔
      (edgePartition ((selIdxs.map fun i => es[i.val]).map IndexedEdge.toWeighted)).rel x y =
        true) :
    2 * nOut ≤ n := by
  let F : Fin nOut → Finset (Fin n) := fun y => Finset.univ.filter fun x => compFn x = lift y
  have hdisj_F : Set.PairwiseDisjoint (Finset.univ : Finset (Fin nOut)) F := fun _ _ _ _ hne =>
    Finset.disjoint_left.mpr fun _ hx₁ hx₂ => by
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
      exact hne (hlift_inj (hx₁.symm.trans hx₂))
  have hcard_ge2 : ∀ y : Fin nOut, 2 ≤ (F y).card := fun y => by
    obtain ⟨eOut, heOut, heOut_inc⟩ := hout_cover y
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp heOut
    have hno := ((isSimple_iff _).mp hes_out_simp).1 ⟨j, by simpa only [List.length_map] using hj⟩
    simp only [edgeEnds, List.getElem_map, IndexedEdge.toWeighted, Sym2.mk_isDiag_iff] at hno
    obtain ⟨e, he_es, he_rem⟩ := List.mem_map.mp (hes_con ▸ hded_sub.subset
      (hes_compact ▸ List.mem_map.mpr ⟨esOut[j]'hj, List.getElem_mem hj, rfl⟩))
    obtain ⟨x₀, hx₀, hinc0⟩ : ∃ x₀ : Fin n, compFn x₀ = lift y ∧ (e.u = x₀ ∨ e.v = x₀) :=
      heOut_inc.elim (fun h => ⟨e.u, (congrArg IndexedEdge.u he_rem).trans (congrArg lift h),
        .inl rfl⟩) fun h => ⟨e.v, (congrArg IndexedEdge.v he_rem).trans (congrArg lift h), .inr rfl⟩
    obtain ⟨idx, hmem_sel, hne_idx, hinc_idx⟩ := hcov_nonloop x₀ ⟨e, he_es, fun huv => hno
      (hlift_inj ((congrArg IndexedEdge.u he_rem).symm.trans ((congrArg compFn huv).trans
        (congrArg IndexedEdge.v he_rem)))), hinc0⟩
    have hcomp_idx : compFn (es[idx.val]).u = compFn (es[idx.val]).v :=
      (hcomp_rel _ _).mpr ((rel_edgePartition_iff_eqvGen _ _ _).mpr (.rel _ _
        ⟨(es[idx.val]).toWeighted, List.mem_map.mpr ⟨es[idx.val], List.mem_map.mpr
          ⟨idx, hmem_sel, rfl⟩, rfl⟩, rfl, rfl⟩))
    let x₁ : Fin n := if (es[idx.val]).u = x₀ then (es[idx.val]).v else (es[idx.val]).u
    have hx₁_ne : x₁ ≠ x₀ := by
      dsimp only [x₁]; split_ifs with h <;> [exact fun h1 => hne_idx (h.trans h1.symm); exact h]
    have hx₁_comp : compFn x₁ = lift y := by
      dsimp only [x₁]; split_ifs with h <;> [rw [← hcomp_idx, h, hx₀];
        exact hcomp_idx.trans ((hinc_idx.resolve_left h) ▸ hx₀)]
    exact (Finset.card_pair hx₁_ne.symm) ▸ Finset.card_le_card fun z hz => by
      simp only [Finset.mem_insert, Finset.mem_singleton, F, Finset.mem_filter, Finset.mem_univ,
        true_and] at hz ⊢
      rcases hz with rfl | rfl <;> assumption
  calc 2 * nOut = ∑ _ ∈ (Finset.univ : Finset (Fin nOut)), 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ y ∈ (Finset.univ : Finset (Fin nOut)), (F y).card :=
      Finset.sum_le_sum fun y _ => hcard_ge2 y
    _ = ((Finset.univ : Finset (Fin nOut)).biUnion F).card := (Finset.card_biUnion hdisj_F).symm
    _ ≤ n := (Finset.card_le_card (Finset.subset_univ _)).trans (Finset.card_fin n).le

private theorem boruvkaStep_word_post {w : ℕ} {d : GraphSlice} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin_lt : d.edgeBase + 4 * d.numEdges ≤ s.frontier)
    (hfit : Fits w (s.frontier + (22 * d.numEdges + 16 * d.numVertices + 4)))
    (hedges : ∀ j < d.numEdges, s.mem (d.edgeBase + 4 * j) < d.numVertices ∧
      s.mem (d.edgeBase + 4 * j + 1) < d.numVertices) :
    let p := (Memory.spec 0).clientResult s (boruvkaPartitionProg d)
    let s₁ := (Memory.spec 0).clientState s (boruvkaPartitionProg d)
    d.edgeBase + 4 * d.numEdges ≤ s₁.frontier ∧ p.compBase + d.numVertices ≤ s₁.frontier ∧
    Fits w (s₁.frontier + (21 * d.numEdges + 3 * p.numComps + 3)) ∧
    (∀ j < d.numEdges, s₁.mem (d.edgeBase + 4 * j) < d.numVertices ∧
      s₁.mem (d.edgeBase + 4 * j + 1) < d.numVertices) ∧
    ∀ u < d.numVertices, s₁.mem (p.compBase + u) < p.numComps := by
  rcases d with ⟨n, m, eb⟩; dsimp only at *
  obtain ⟨es, hlen, hin⟩ := exists_indexedEdges_of_mem_lt hedges
  have hpart_ft := boruvkaPartitionProg_spec h16 hwf hin
    (by rw [hlen]; exact hin_lt) (by rw [hlen]; exact hfit.of_le (by omega))
  rw [show (⟨n, es.length, eb⟩ : GraphSlice) = ⟨n, m, eb⟩ from by rw [hlen]] at hpart_ft
  obtain ⟨_, _, hmod₁, hfr₁, _, _, _, hcc_fr, _, _, hcc_le, _, _, compFn, _, _, _, _, _, _,
      hcomp_mem, _⟩ := framedTriple_iff_realization.mp hpart_ft
  rw [hlen] at hfr₁
  refine ⟨Nat.le_trans hin_lt hmod₁.1, hcc_fr, hfit.of_le (by omega), fun j hj => by
    rw [hmod₁.mem_eq_of_not_mem (by omega) (Set.notMem_empty _),
      hmod₁.mem_eq_of_not_mem (by omega) (Set.notMem_empty _)]
    exact hedges j hj, fun u hu => hcomp_mem ⟨u, hu⟩ ▸ (compFn ⟨u, hu⟩).isLt⟩

/-- Uniform `Realizes .exact` certificate for `boruvkaStepProg` with `work = 0`. -/
theorem realizes_boruvkaStepProg : Realizes .exact
    boruvkaStepProg WordEncoding.encode WordEncoding.encode
    (fun w g s => Fits w 16 ∧ g.edgeBase + 4 * g.numEdges ≤ s.frontier ∧
      Fits w (s.frontier + (22 * g.numEdges + 16 * g.numVertices + 4)) ∧
      ∀ j < g.numEdges, s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
        s.mem (g.edgeBase + 4 * j + 1) < g.numVertices)
    (fun _ _ => 0) := by
  unfold boruvkaStepProg
  realize [realizes_boruvkaPartitionProg, realizes_boruvkaShrinkProg]
  all_goals
    obtain ⟨h16, hin_lt, hfit, hedges⟩ := h
    first
    | exact h16 | exact hin_lt | exact hfit.of_le (by omega) | exact hedges
    | (obtain ⟨a, b, c, e, f⟩ := boruvkaStep_word_post h16 hmem hin_lt hfit hedges
       first | exact a | exact b | exact c | exact e | exact f)

/-- Framed specification for `boruvkaStepProg`: executes one Borůvka contraction round
([PettieRamachandran2002], Section 2.1, p. 18) in at most `76 * es.length + 61 * n + 34` memory
operations using at most `22 * es.length + 16 * n + 4` words while leaving cells below
`s.frontier` untouched, reducing the remaining vertex count to at most half of the total input
vertices after dropping isolated output vertices (`2 * res.outVertices ≤ n`), and preserving MSF
liftability. Unlike [PettieRamachandran2002] (which assumes distinct weights and groups two
rounds as `Boruvka2`), this step contracts a single round over indexed multigraphs with tied
weights broken deterministically by smallest list index. -/
theorem boruvkaStepProg_spec {w n edgeBase : ℕ} {es : List (IndexedEdge n)}
    {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hin_lt : edgeBase + 4 * es.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + (22 * es.length + 16 * n + 4))) :
    Memory.FramedTriple w s (boruvkaStepProg ⟨n, es.length, edgeBase⟩)
      (76 * es.length + 61 * n + 34) ∅ fun res s' =>
        s'.frontier ≤ s.frontier + (22 * es.length + 16 * n + 4) ∧
        s.frontier ≤ res.selBase ∧
        res.selBase + 4 * res.selCount ≤ s'.frontier ∧
        s.frontier ≤ res.outBase ∧
        res.outBase + 4 * res.outEdges ≤ s'.frontier ∧
        2 * res.outVertices ≤ n ∧ res.outEdges ≤ es.length ∧
        res.selCount ≤ n ∧ res.selCount ≤ es.length ∧ Memory.WellFormed w s' ∧
        ∃ (selIdxs outIdxs : List (Fin es.length)) (esOut : List (IndexedEdge res.outVertices)),
          selIdxs.length = res.selCount ∧ selIdxs.Nodup ∧
          outIdxs.length = res.outEdges ∧ outIdxs.Nodup ∧ esOut.length = res.outEdges ∧
          (∀ i ∈ selIdxs, i ∉ outIdxs) ∧
          HoldsIndexedEdges res.selBase (selIdxs.map fun i => es[i.val]) s'.mem ∧
          HoldsIndexedEdges res.outBase esOut s'.mem ∧
          IsSimple (edgeEnds (esOut.map IndexedEdge.toWeighted)) ∧
          esOut.map IndexedEdge.weight = outIdxs.map (fun i => es[i.val].weight) ∧
          esOut.map IndexedEdge.id = outIdxs.map (fun i => es[i.val].id) ∧
          (∀ L_out : List (IndexedEdge res.outVertices),
            L_out.Subperm esOut →
            IsMinSpanningForest (esOut.map IndexedEdge.toWeighted)
              (L_out.map IndexedEdge.toWeighted) →
            ∃ L_orig : List (IndexedEdge n),
              (selIdxs.map (fun i => es[i.val]) ++ L_orig).Subperm es ∧
              L_orig.map IndexedEdge.id = L_out.map IndexedEdge.id ∧
              IsMinSpanningForest (es.map IndexedEdge.toWeighted)
                ((selIdxs.map (fun i => es[i.val]) ++ L_orig).map IndexedEdge.toWeighted)) ∧
          (∀ idx ∈ selIdxs, ∃ x : Fin n, IsVertexMinEdge es x idx) ∧
          ∀ x : Fin n, (∃ e ∈ es, e.u ≠ e.v ∧ (e.u = x ∨ e.v = x)) →
            ∃ idx ∈ selIdxs, IsVertexMinEdge es x idx := by
  dsimp only [boruvkaStepProg]
  refine (Memory.FramedTriple.bind_same (c₂ := 66 * es.length + 11 * n + 23)
    ((FramedTriple.with_modifies (holdsIndexedEdges_frame_mem
      (boruvkaPartitionProg_spec h16 hwf hin hin_lt (hfit.of_le (by omega)))
      hin (Set.empty_disjoint _) hin_lt)).mono le_rfl fun p s₁
        ⟨hmod₁, ⟨hfr₁, hsel_ge, hsel_fr1, _, hcc_fr1, hsel_cn, hsel_cm, _, hwf₁, selIdxs, compFn,
          hsl_len, hnd_sel, hsel_sub, hsel_msf, hsel_holds, hcov_nonloop, hcomp_mem, hcomp_surj,
          hcomp_rel, hsel_sound, hcov_min⟩, hin₁⟩ => ?_)).mono (by omega) fun _ _ h => h
  refine (Memory.FramedTriple.bind_same (c₂ := 0) ((FramedTriple.with_modifies
    (holdsIndexedEdges_frame_mem (boruvkaShrinkProg_spec h16 hwf₁ hin₁
      (Nat.le_trans hin_lt hmod₁.1) hcomp_mem hcc_fr1 (hfit.of_le (by omega))) hsel_holds
      (Set.empty_disjoint _) (by rw [List.length_map, hsl_len]; exact hsel_fr1))).mono
      le_rfl fun out s₂ ⟨hmod₂, ⟨hfr₂, hout_ge, hout_fr2, _, hne_le, hwf₂, esCon, esDedup, lift,
        esOut, hes_con, hded_sub, hded_eq, hded_simp, hlift_inj, hlen_out, hout_holds, hout_cover,
        hes_compact⟩, hsel_holds2⟩ => ?_)).mono (by omega) fun _ _ h => h
  let remapper (e : IndexedEdge n) : IndexedEdge p.numComps :=
    ⟨compFn e.u, compFn e.v, e.weight, e.id⟩
  have hes_out_simp := compactVertices_isSimple hes_compact hded_simp
  have hfull : (List.finRange es.length).map (fun i : Fin es.length => remapper es[i.val]) =
      es.map remapper := List.ext_getElem (by simp only [List.length_map, List.length_finRange])
    fun _ _ _ => by simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk]
  obtain ⟨outIdxs, hout_sub_range, hout_map_eq⟩ :=
    ((hfull ▸ hes_con ▸ hded_sub) :
      esDedup.Subperm ((List.finRange es.length).map fun i => remapper es[i.val])).exists_map
  have hmap_eq := hes_compact.trans hout_map_eq.symm
  have hout_len : outIdxs.length = out.numEdges := by
    have h1 := congrArg List.length hmap_eq; simp only [List.length_map] at h1; rw [← h1, hlen_out]
  have hdisj_idx : ∀ i ∈ selIdxs, i ∉ outIdxs := fun i hi_sel hi_out => by
    have hcomp_eq : compFn es[i.val].u = compFn es[i.val].v :=
      (hcomp_rel _ _).mpr ((rel_edgePartition_iff_eqvGen _ _ _).mpr (.rel _ _ ⟨es[i.val].toWeighted,
        List.mem_map.mpr ⟨es[i.val], List.mem_map.mpr ⟨i, hi_sel, rfl⟩, rfl⟩, rfl, rfl⟩))
    obtain ⟨eOut, heOut, he_eq⟩ := List.mem_map.mp
      (hmap_eq ▸ List.mem_map.mpr ⟨i, hi_out, rfl⟩)
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp heOut
    have hno := ((isSimple_iff _).mp hes_out_simp).1 ⟨j, by simpa only [List.length_map] using hj⟩
    simp only [edgeEnds, List.getElem_map, IndexedEdge.toWeighted, Sym2.mk_isDiag_iff] at hno
    exact hno (hlift_inj ((congrArg IndexedEdge.u he_eq).trans
      (hcomp_eq.trans (congrArg IndexedEdge.v he_eq).symm)))
  exact Memory.FramedTriple.pure ⟨by omega, hsel_ge, Nat.le_trans hsel_fr1 hmod₂.1,
    Nat.le_trans hmod₁.1 hout_ge, hout_fr2,
    boruvkaStep_two_mul_le hes_con hded_sub hlift_inj hout_cover hes_compact hes_out_simp
      hcov_nonloop hcomp_rel,
    hne_le, hsel_cn, hsel_cm, hwf₂, selIdxs, outIdxs, esOut, hsl_len, hnd_sel, hout_len,
    hout_sub_range.nodup (List.nodup_finRange _), hlen_out, hdisj_idx, hsel_holds2,
    hout_holds, hes_out_simp,
    by simpa only [List.map_map, Function.comp_def, remapper] using
      congrArg (List.map IndexedEdge.weight) hmap_eq,
    by simpa only [List.map_map, Function.comp_def, remapper] using
      congrArg (List.map IndexedEdge.id) hmap_eq,
    fun L_out hL_sub hL_msf => boruvkaStepProg_lift_msf hsel_sub hsel_msf hcomp_surj hcomp_rel
      hes_con hded_sub hded_eq hded_simp hlift_inj hes_compact hL_sub hL_msf,
    hsel_sound, hcov_min⟩

end Cslib.Algorithms.WordRAM.MinimumSpanningForest
