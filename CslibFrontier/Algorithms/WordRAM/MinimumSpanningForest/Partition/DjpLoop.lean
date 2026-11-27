/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.Partition.DjpStep
import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.ExtractMin
import CslibFrontier.DataStructure.Memory.Frame
import CslibFrontier.Tactic.UpdateSimp
import CslibFrontier.Tactic.ValidProg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Dynamic Soft-Heap DJP Round Invariants, Step, and Loop Specifications

Verifies round initialization (`partRoundInit_spec`), single dynamic-DJP extraction/dispatch step
(`partDjpStep_spec`), and the bounded while-loop specification (`partDjpLoop_spec`) for the
`ε = 1 / 16` (`partRankThreshold = 8`) partition subroutine of [PettieRamachandran2002],
Section 3.2.

All loop inductions reuse `LoopFrame.boundedWhile_rat_witness_spec`, Soft-Heap extraction reuses
`SoftHeap.{shExtractMin_spec, SHInv}`, and tree growth reuses `DynamicDJPTree` and `extendDJP`.

## Main definitions

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DjpWitness`: complete round state invariant
  relating Word-RAM memory, Soft-Heap forest, and `DynamicDJPTree`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.djpRank`: termination rank for `partDjpLoop`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.djpPot`: amortized `ℚ`-potential combining
  `totalPhi partRankThreshold`, remaining CSR degree (`2450 * remDeg`), and headroom (`275 * ...`).

## Main results

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.partDjpStep_spec`: single-step preservation,
  `djpRank` decrease, and amortized potential inequality.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.partRoundInit_spec`: round initialization and
  root expansion specification with amortized cost bound `+15`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.partDjpLoop_spec`: full while-loop specification
  producing a terminal `DjpWitness` within initial `djpPot W₀`.
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Query.MinimumSpanningForest
open Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap

/-! ## Three-Write Round Update Helper -/

private def write3Mem (bufBase n size cid v : ℕ) (mem : ℕ → ℕ) : ℕ → ℕ :=
  Function.update
    (Function.update (Function.update mem (bufBase + 3 * n + size) v) (bufBase + n + v) cid)
    (bufBase + 2 * n + v) size

private theorem write3Mem_wf {w bufBase n size cid v : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hv : Fits w v) (hcid : Fits w cid) (hsz : Fits w size) :
    Memory.WellFormed w ⟨write3Mem bufBase n size cid v s.mem, s.frontier⟩ := by
  refine ⟨hwf.frontier_fits, fun a => ?_⟩; dsimp only [write3Mem]
  simp only [Function.update_apply]
  split_ifs <;> first | exact hsz | exact hcid | exact hv | exact hwf.mem_fits a

private theorem write3Mem_agree_outside {bufBase n size cid v x : ℕ} {mem : ℕ → ℕ}
    (hx1 : x ≠ bufBase + 3 * n + size) (hx2 : x ≠ bufBase + n + v)
    (hx3 : x ≠ bufBase + 2 * n + v) : write3Mem bufBase n size cid v mem x = mem x := by
  dsimp only [write3Mem]
  rw [Function.update_of_ne hx3, Function.update_of_ne hx2, Function.update_of_ne hx1]

private theorem write3Mem_in_range {bufBase n size cid v x : ℕ} {mem : ℕ → ℕ}
    (hv_lt : v < n) (hsz_lt : size < n) (hmod : write3Mem bufBase n size cid v mem x ≠ mem x) :
    bufBase + n ≤ x ∧ x < bufBase + 4 * n :=
  by_contra fun _ => hmod (write3Mem_agree_outside (by omega) (by omega) (by omega))

/-! ## Dynamic-DJP Round Witness, Termination Rank, and Potential -/

/-- Complete state invariant maintained across `partRoundInit`, `partDjpStep`, and
`partDjpLoop` relative to pre-round state `s₀`. -/
structure DjpWitness {w n : ℕ} (L : PartLayout w n) (s₀ : Memory.State)
    (dead0 inCur0 edgeState0 : ℕ → ℕ) (cid ic0 nc0 tLen0 : ℕ) (u : Fin n)
    (a : PartDjpState) (s : Memory.State) where
  /-- Logical Soft-Heap root forest. -/
  roots : List SHTree
  /-- Soft-Heap birth counts per rank. -/
  created : ℕ → ℕ
  /-- Dynamic DJP tree built so far in the current round. -/
  D : DynamicDJPTree n
  /-- Original `IndexedEdge` records corresponding to `D.treeEdges`. -/
  treeIndexed : List (IndexedEdge n)
  /-- Frontier invariant preserving the pre-round allocated workspace. -/
  hfr : s.frontier = L.bufBase + (14 * n + 14 * L.es.length)
  /-- Modified cells lie in the Soft-Heap slice, `[inCur, compVerts)`, or round DJP slice. -/
  hmod : ∀ x, s.mem x ≠ s₀.mem x →
    InSHPool ic0 nc0 (2 * L.es.length) (4 * L.es.length)
      ⟨L.itemBase, L.nodeBase, 0, ic0, nc0, partRankThreshold⟩ x ∨
    (L.bufBase + n ≤ x ∧ x < L.bufBase + 4 * n) ∨
    (L.bufBase + 10 * n + 4 * tLen0 ≤ x ∧ x < L.bufBase + 10 * n + 4 * a.tLen)
  /-- Soft-Heap item base invariant. -/
  hib : a.sh.itemBase = L.itemBase
  /-- Soft-Heap node base invariant. -/
  hnb : a.sh.nodeBase = L.nodeBase
  /-- Soft-Heap rank threshold invariant (`partRankThreshold = 8`). -/
  hrt : a.sh.rankThreshold = partRankThreshold
  /-- Soft-Heap item count lower bound (`ic0 ≤ itemCount`). -/
  hic_ge : ic0 ≤ a.sh.itemCount
  /-- Soft-Heap item count capacity bound (`itemCount ≤ 2 * m`). -/
  hic_le : a.sh.itemCount ≤ 2 * L.es.length
  /-- Soft-Heap structural invariant. -/
  hsh : SHInv w ic0 nc0 (2 * L.es.length) (4 * L.es.length) a.sh roots created s
  /-- Root of `D` is `u`. -/
  hroot : D.root = u
  /-- Vertex count matches `D.numSteps + 1`. -/
  hsize : a.size = D.numSteps + 1
  /-- Vertex count does not exceed `maxsize`. -/
  hsize_le : a.size ≤ L.maxsize
  /-- Cumulative DJP tree edge count matches `tLen0 + D.numSteps`. -/
  htlen : a.tLen = tLen0 + D.numSteps
  /-- Cumulative DJP tree edge count does not exceed `n`. -/
  htlen_le : a.tLen ≤ n
  /-- Dead-vertex credit invariant for `tLen`. -/
  htlen_dead : a.tLen ≤ (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)).card + D.numSteps
  /-- Tree edge list length equals `D.numSteps`. -/
  htree_len : treeIndexed.length = D.numSteps
  /-- Weighted projection of `treeIndexed` equals `D.treeEdges`. -/
  htree_w : treeIndexed.map IndexedEdge.toWeighted = D.treeEdges
  /-- Every edge in `treeIndexed` came from an active edge in `L.es`. -/
  htree_src : ∀ e ∈ treeIndexed, ∃ eIdx : Fin L.es.length,
    e = (L.es[eIdx.val]'eIdx.isLt) ∧ edgeState0 eIdx.val = 0
  /-- `treeIndexed` is stored in memory at `bufBase + 10 * n + 4 * tLen0`. -/
  htree_mem : HoldsIndexedEdges (L.bufBase + 10 * n + 4 * tLen0) treeIndexed s.mem
  /-- `compVerts[0..size)` holds `djpVertsList D`. -/
  hverts_mem : ∀ k (hk : k < a.size), s.mem (L.bufBase + 3 * n + k) =
    ((djpVertsList D)[k]'(by rw [djpVertsList_length]; omega)).val
  /-- Every vertex in `D` has `inCur = cid` and consistent `localIdx`. -/
  hincur_in : ∀ x : Fin n, x ∈ D.treeVerts D.numSteps → s.mem (L.bufBase + n + x.val) = cid ∧
    ∃ k < a.size, s.mem (L.bufBase + 3 * n + k) = x.val ∧ s.mem (L.bufBase + 2 * n + x.val) = k
  /-- Vertices outside `D` preserve pre-round `inCur0`. -/
  hincur_out : ∀ x : Fin n, x ∉ D.treeVerts D.numSteps →
    s.mem (L.bufBase + n + x.val) = inCur0 x.val
  /-- Hitting an already-dead vertex stops the loop with `hitPrev = 1, cont = 0`. -/
  hstop_dead : ∀ x : Fin n, x ∈ D.treeVerts D.numSteps → dead0 x.val ≠ 0 →
    a.hitPrev = 1 ∧ a.cont = 0 ∧ 1 ≤ D.numSteps ∧
      (∀ h1 : 1 ≤ D.numSteps, x = D.vOut ⟨D.numSteps - 1, by omega⟩)
  /-- Nonzero `hitPrev` implies the last added vertex `vOut` was dead. -/
  hhit_prev : a.hitPrev ≠ 0 → a.hitPrev = 1 ∧ a.cont = 0 ∧ 1 ≤ D.numSteps ∧
    (∀ h1 : 1 ≤ D.numSteps, dead0 (D.vOut ⟨D.numSteps - 1, by omega⟩).val ≠ 0)
  /-- Zero `hitPrev` means all vertices of `D` were initially alive. -/
  hno_hit : a.hitPrev = 0 → ∀ x ∈ D.treeVerts D.numSteps, dead0 x.val = 0
  /-- Soft-Heap capacity headroom bounded by unexpanded CSR half-edges. -/
  hcap_rem : a.sh.itemCount + remDeg n L.offBase s.mem
    (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0) ∪ D.treeVerts D.numSteps) ≤
    2 * L.es.length
  /-- Live Soft-Heap items carry distinct edge IDs. -/
  hnd_edge : ((forestItems roots).map SHItem.val).Nodup
  /-- Every Soft-Heap entry corresponds to an active edge incident to `D`. -/
  hent_prop : ∀ p ∈ forestEntries roots, ∃ eIdx : Fin L.es.length, p.1.val = eIdx.val ∧
    p.1.origKey = (L.es[eIdx.val]'eIdx.isLt).weight ∧ p.1.origKey ≤ p.2 ∧
    edgeState0 eIdx.val = 0 ∧
    ((L.es[eIdx.val]'eIdx.isLt).u ∈ D.treeVerts D.numSteps ∨
     (L.es[eIdx.val]'eIdx.isLt).v ∈ D.treeVerts D.numSteps)
  /-- While continuing (`cont ≠ 0`), every active edge crossing `D` is in the Soft Heap. -/
  hcont_cov : a.cont ≠ 0 → ∀ eIdx : Fin L.es.length, edgeState0 eIdx.val = 0 →
    ((L.es[eIdx.val]'eIdx.isLt).u ∈ D.treeVerts D.numSteps ↔
      (L.es[eIdx.val]'eIdx.isLt).v ∉ D.treeVerts D.numSteps) →
    ∃ p ∈ forestEntries roots, p.1.val = eIdx.val
  /-- Every active edge crossing some prefix of `D` and not internal stays in the Soft Heap. -/
  hcut_cov : ∀ eIdx : Fin L.es.length, edgeState0 eIdx.val = 0 →
    ¬((L.es[eIdx.val]'eIdx.isLt).u ∈ D.treeVerts D.numSteps ∧
      (L.es[eIdx.val]'eIdx.isLt).v ∈ D.treeVerts D.numSteps) →
    (∃ s_step : Fin D.numSteps, (L.es[eIdx.val]'eIdx.isLt).u ∈ D.treeVerts s_step.val ↔
      (L.es[eIdx.val]'eIdx.isLt).v ∉ D.treeVerts s_step.val) →
    ∃ p ∈ forestEntries roots, p.1.val = eIdx.val
  /-- Any surviving item crossing prefix `s_step` has corrupted key at least `D.wPop s_step`. -/
  hwpop_fut : ∀ s_step : Fin D.numSteps, ∀ p ∈ forestEntries roots,
    (∃ hlt : p.1.val < L.es.length, ((L.es[p.1.val]'hlt).u ∈ D.treeVerts s_step.val ↔
      (L.es[p.1.val]'hlt).v ∉ D.treeVerts s_step.val)) → D.wPop s_step ≤ p.2
  /-- Early stop while alive and below `maxsize` implies no active cut edge remains. -/
  hempty_stop : a.cont = 0 → a.hitPrev = 0 → a.size < L.maxsize →
    ∀ eIdx : Fin L.es.length, edgeState0 eIdx.val = 0 →
      ¬((L.es[eIdx.val]'eIdx.isLt).u ∈ D.treeVerts D.numSteps ↔
        (L.es[eIdx.val]'eIdx.isLt).v ∉ D.treeVerts D.numSteps)
  /-- Continuation implies strict headroom below `maxsize`. -/
  hcont_size : a.cont ≠ 0 → a.size < L.maxsize

section WitnessVars

variable {w n : ℕ} {L : PartLayout w n} {s₀ : Memory.State}
  {dead0 inCur0 edgeState0 : ℕ → ℕ} {cid ic0 nc0 tLen0 : ℕ} {u : Fin n}
  {a : PartDjpState} {s : Memory.State}

/-- Termination measure for `partDjpLoop`. -/
@[expose] def djpRank (W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s) : ℕ :=
  if a.cont = 0 then 0 else 1 + (2 * L.es.length - a.sh.itemCount) + (forestItems W.roots).length

/-- Amortized `ℚ`-potential (`totalPhi 8 + 2450 * remDeg + 275 * headroom`) for `partDjpLoop`. -/
@[expose] def djpPot (W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s) : ℚ :=
  totalPhi partRankThreshold W.roots + 2450 * (remDeg n L.offBase s.mem
    (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0) ∪ W.D.treeVerts W.D.numSteps) : ℚ) +
  275 * ((2 * L.es.length - a.sh.itemCount : ℕ) + (forestItems W.roots).length : ℚ) +
  (if a.cont = 0 then 0 else 10)

/-- Addresses outside the Soft Heap, `[inCur, compVerts)`, and round DJP tree slice agree
with pre-round memory `s₀`. -/
theorem DjpWitness.agree_outside_mod
    (W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s) {x : ℕ}
    (h1 : ¬InSHPool ic0 nc0 (2 * L.es.length) (4 * L.es.length)
      ⟨L.itemBase, L.nodeBase, 0, ic0, nc0, partRankThreshold⟩ x)
    (h2 : ¬(L.bufBase + n ≤ x ∧ x < L.bufBase + 4 * n))
    (h3 : ¬(L.bufBase + 10 * n + 4 * tLen0 ≤ x ∧ x < L.bufBase + 10 * n + 4 * a.tLen)) :
    s.mem x = s₀.mem x := by_contra fun hne => (W.hmod x hne).elim h1 fun h => h.elim h2 h3

private theorem djpWitness_agree_below_pool
    (W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s) :
    ∀ x < L.itemBase, s.mem x = s₀.mem x := fun x hx =>
  W.agree_outside_mod (fun h => by
      rcases PartLayout.inSHPool_bounds (h := ⟨L.itemBase, L.nodeBase, 0, ic0, nc0,
        partRankThreshold⟩) h with ⟨h1, _⟩ | ⟨h1, _⟩
      · dsimp only at h1; omega
      · dsimp only at h1; have := L.hit_nd; omega)
    (fun _ => by have := L.hit_nd; have := L.hnd_buf; omega)
    (fun _ => by have := L.hit_nd; have := L.hnd_buf; omega)

/-- Preserves `HoldsUndirCSR` under any `DjpWitness`. -/
theorem djpWitness_csr (W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s)
    (hcsr₀ : HoldsUndirCSR L.offBase L.adjBase L.es s₀.mem) :
    HoldsUndirCSR L.offBase L.adjBase L.es s.mem :=
  (L.congr_below_itemBase (djpWitness_agree_below_pool W)).2 hcsr₀

/-- Preserves `HoldsIndexedEdges` under any `DjpWitness`. -/
theorem djpWitness_edges (W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s)
    (hin₀ : HoldsIndexedEdges L.edgeBase L.es s₀.mem) :
    HoldsIndexedEdges L.edgeBase L.es s.mem :=
  (L.congr_below_itemBase (djpWitness_agree_below_pool W)).1 hin₀

/-- Preserves `dead0` under any `DjpWitness`. -/
theorem djpWitness_dead (W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s)
    (hdead₀ : ∀ x < n, s₀.mem (L.bufBase + x) = dead0 x) :
    ∀ x < n, s.mem (L.bufBase + x) = dead0 x := fun x hx =>
  (W.agree_outside_mod (fun h => by rcases L.inSHPool_lt_bufBase rfl rfl h with ⟨_, h2⟩; omega)
    (by omega) (by omega)).trans (hdead₀ x hx)

/-- Preserves `edgeState0` under any `DjpWitness`. -/
theorem djpWitness_edgeState (W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s)
    (hedge₀ : ∀ i < L.es.length, s₀.mem (L.bufBase + 14 * n + i) = edgeState0 i) :
    ∀ i < L.es.length, s.mem (L.bufBase + 14 * n + i) = edgeState0 i := fun i hi =>
  (W.agree_outside_mod (fun h => by rcases L.inSHPool_lt_bufBase rfl rfl h with ⟨_, h2⟩; omega)
    (by omega) (fun _ => by have := W.htlen_le; omega)).trans (hedge₀ i hi)

/-! ## Shared Step Plumbing and Framing Helpers -/

private abbrev DjpModRange {w n : ℕ} (L : PartLayout w n) (ic0 nc0 tLen0 sz x : ℕ) : Prop :=
  InSHPool ic0 nc0 (2 * L.es.length) (4 * L.es.length)
    ⟨L.itemBase, L.nodeBase, 0, ic0, nc0, partRankThreshold⟩ x ∨
  (L.bufBase + n ≤ x ∧ x < L.bufBase + 4 * n) ∨
  (L.bufBase + 10 * n + 4 * tLen0 ≤ x ∧ x < L.bufBase + 10 * n + 4 * sz)

private abbrev DjpStepPost (W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s)
    {α : Type} (prog : Memory.Prog PartDjpState)
    (safe : ℕ → α → Memory.State → Prop) (arg : α) (s₁ : Memory.State)
    (extraCost : ℚ) (roots₁ : List SHTree) : Prop :=
  safe w arg s₁ ∧ (Memory.spec w).ValidHistory s₁ ((Memory.spec w).clientHistory s₁ prog) ∧
  ((Memory.spec 0).clientState s₁ prog).frontier = s.frontier ∧
  (∀ x, ¬(InSHPool ic0 nc0 (2 * L.es.length) (4 * L.es.length)
    ⟨L.itemBase, L.nodeBase, 0, ic0, nc0, partRankThreshold⟩ x ∨
    (L.bufBase + n ≤ x ∧ x < L.bufBase + 4 * n) ∨
    (L.bufBase + 10 * n ≤ x ∧ x < L.bufBase + 14 * n)) →
    ((Memory.spec 0).clientState s₁ prog).mem x = s₁.mem x) ∧
  ∃ W' : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u
      ((Memory.spec 0).clientResult s₁ prog) ((Memory.spec 0).clientState s₁ prog),
    djpPot W' + (memoryCost prog s₁ : ℚ) + extraCost ≤
      djpPot W + (totalPhi partRankThreshold roots₁ - totalPhi partRankThreshold W.roots) ∧
    djpRank W' < djpRank W

private theorem hent_prop_lift
    (W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s)
    {h₁ : SHHandle} {roots₁ : List SHTree} {s₁ : Memory.State}
    (hsh₁ : SHInv w ic0 nc0 (2 * L.es.length) (4 * L.es.length) h₁ roots₁ W.created s₁)
    (hent₁ : ∀ p ∈ forestEntries roots₁, ∃ c₀, (p.1, c₀) ∈ forestEntries W.roots ∧ c₀ ≤ p.2)
    (S : Finset (Fin n)) (hsub : W.D.treeVerts W.D.numSteps ⊆ S) :
    ∀ p ∈ forestEntries roots₁, ∃ e' : Fin L.es.length,
      p.1.val = e'.val ∧ p.1.origKey = (L.es[e'.val]'e'.isLt).weight ∧ p.1.origKey ≤ p.2 ∧
      edgeState0 e'.val = 0 ∧ ((L.es[e'.val]'e'.isLt).u ∈ S ∨ (L.es[e'.val]'e'.isLt).v ∈ S) :=
  fun p hp => by
  rcases hent₁ p hp with ⟨c₀, hc₀, _⟩
  rcases W.hent_prop (p.1, c₀) hc₀ with ⟨e', h1, h2, _, h4, h5⟩
  exact ⟨e', h1, h2, hsh₁.origKey_le_ckey p hp, h4, h5.imp (fun hu => hsub hu) (fun hv => hsub hv)⟩

private theorem djpWitness_mem_of_inCur_cid
    (W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s)
    (hincur₀_ne : ∀ x < n, inCur0 x ≠ cid) (v : Fin n)
    (hv : s.mem (L.bufBase + n + v.val) = cid) : v ∈ W.D.treeVerts W.D.numSteps :=
  by_contra fun hnin => hincur₀_ne v.val v.isLt ((W.hincur_out v hnin).symm.trans hv)

private theorem djp_inCur_transport {n bufBase cid : ℕ} {inCur0 : ℕ → ℕ}
    {D : DynamicDJPTree n} {sz : ℕ} {s s' : Memory.State} (hsz : sz ≤ D.numSteps + 1)
    (hagree : ∀ x, bufBase ≤ x → x < bufBase + 4 * n → s'.mem x = s.mem x)
    (hin : ∀ x : Fin n, x ∈ D.treeVerts D.numSteps → s.mem (bufBase + n + x.val) = cid ∧
      ∃ k < sz, s.mem (bufBase + 3 * n + k) = x.val ∧ s.mem (bufBase + 2 * n + x.val) = k)
    (hout : ∀ x : Fin n, x ∉ D.treeVerts D.numSteps → s.mem (bufBase + n + x.val) = inCur0 x.val) :
    (∀ x : Fin n, x ∈ D.treeVerts D.numSteps → s'.mem (bufBase + n + x.val) = cid ∧
      ∃ k < sz, s'.mem (bufBase + 3 * n + k) = x.val ∧ s'.mem (bufBase + 2 * n + x.val) = k) ∧
    (∀ x : Fin n, x ∉ D.treeVerts D.numSteps → s'.mem (bufBase + n + x.val) = inCur0 x.val) :=
  ⟨fun x hx => by
    rcases hin x hx with ⟨h1, k, hk, h2, h3⟩; have := djp_numSteps_add_one_le D
    exact ⟨(hagree _ (by omega) (by omega)).trans h1, k, hk,
      (hagree _ (by omega) (by omega)).trans h2, (hagree _ (by omega) (by omega)).trans h3⟩,
   fun x hx => (hagree _ (by omega) (by omega)).trans (hout x hx)⟩

private theorem inSHPool_mod_trans {w n ic₀ nc₀ tLen₀ sz' : ℕ} {L : PartLayout w n}
    {s₀ s s' : Memory.State} {h₀ : SHHandle} (hib : h₀.itemBase = L.itemBase)
    (hnb : h₀.nodeBase = L.nodeBase)
    (hs : ∀ x, s.mem x ≠ s₀.mem x → DjpModRange L ic₀ nc₀ tLen₀ sz' x)
    (hs' : ∀ x, s'.mem x ≠ s.mem x → InSHPool ic₀ nc₀ (2 * L.es.length) (4 * L.es.length) h₀ x) :
    ∀ x, s'.mem x ≠ s₀.mem x → DjpModRange L ic₀ nc₀ tLen₀ sz' x := fun x hx => by
  by_cases hdiff : s'.mem x = s.mem x
  · exact hs x (hdiff ▸ hx)
  · exact .inl (by simpa only [InSHPool, hib, hnb] using hs' x hdiff)

private theorem write3Mem_incur {n bufBase sz cid : ℕ} {inCur0 : ℕ → ℕ}
    {S : Finset (Fin n)} {vNew : Fin n} (hv_not : vNew ∉ S) (hsz_lt : sz < n) {mem : ℕ → ℕ}
    (hin : ∀ x : Fin n, x ∈ S → mem (bufBase + n + x.val) = cid ∧
      ∃ k < sz, mem (bufBase + 3 * n + k) = x.val ∧ mem (bufBase + 2 * n + x.val) = k)
    (hout : ∀ x : Fin n, x ∉ S → mem (bufBase + n + x.val) = inCur0 x.val) :
    let m' := write3Mem bufBase n sz cid vNew.val mem
    (∀ x : Fin n, x ∈ insert vNew S → m' (bufBase + n + x.val) = cid ∧
      ∃ k < sz + 1, m' (bufBase + 3 * n + k) = x.val ∧ m' (bufBase + 2 * n + x.val) = k) ∧
    (∀ x : Fin n, x ∉ insert vNew S → m' (bufBase + n + x.val) = inCur0 x.val) := by
  intro m'; refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rcases Finset.mem_insert.mp hx with rfl | hx_old
    · refine ⟨by dsimp only [m', write3Mem]; rw [Function.update_of_ne (by omega),
          Function.update_self], sz, Nat.lt_succ_self _,
        by dsimp only [m', write3Mem]; rw [Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_self],
        by dsimp only [m', write3Mem]; rw [Function.update_self]⟩
    · rcases hin x hx_old with ⟨h1, k, hk, h2, h3⟩
      have hne : x.val ≠ vNew.val := fun h => hv_not (Fin.ext h ▸ hx_old)
      refine ⟨(write3Mem_agree_outside (by omega) (by omega) (by omega)).trans h1, k,
        Nat.lt_succ_of_lt hk, (write3Mem_agree_outside (by omega) (by omega) (by omega)).trans h2,
        (write3Mem_agree_outside (by omega) (by omega) (by omega)).trans h3⟩
  · rw [Finset.mem_insert, not_or] at hx
    have hne : x.val ≠ vNew.val := fun h => hx.1 (Fin.ext h)
    exact (write3Mem_agree_outside (by omega) (by omega) (by omega)).trans (hout x hx.2)

private theorem edge_cross_insert_imp {n cid : ℕ} {e : IndexedEdge n} {S : Finset (Fin n)}
    {vOut : Fin n} {inCur inCur0 : ℕ → ℕ}
    (hout : ∀ x : Fin n, x ∉ insert vOut S → inCur x.val = inCur0 x.val)
    (hne : ∀ x < n, inCur0 x ≠ cid) (hu_old : e.u ∉ S) (hv_old : e.v ∉ S)
    (hcross : e.u ∈ insert vOut S ↔ e.v ∉ insert vOut S) :
    (e.u = vOut ∧ inCur e.v.val ≠ cid) ∨ (e.v = vOut ∧ inCur e.u.val ≠ cid) := by
  by_cases hu : e.u = vOut
  · exact .inl ⟨hu, fun h => hne _ e.v.isLt
      ((hout _ (hcross.mp (hu ▸ Finset.mem_insert_self _ _))).symm.trans h)⟩
  · have hu_new : e.u ∉ insert vOut S := by simp [Finset.mem_insert, hu, hu_old]
    have hv_new : e.v ∈ insert vOut S := by_contra fun h => hu_new (hcross.mpr h)
    exact .inr ⟨(Finset.mem_insert.mp hv_new).elim id (fun h => absurd h hv_old),
      fun h => hne _ e.u.isLt ((hout _ hu_new).symm.trans h)⟩

private theorem djpPot_addVert_arith {P' P₁ P₀ R' R₀ deg A' B' A₀ B₁ B₀ C : ℚ}
    (hc : C + P' ≤ P₁ + 14 + 2450 * deg) (hr : R' + deg = R₀)
    (hic : A' + B' = A₀ + B₁) (hb : B₀ = B₁ + 1) :
    (P' + 2450 * R' + 275 * (A' + B') + 10) + C + 4 + 251 ≤
      (P₀ + 2450 * R₀ + 275 * (A₀ + B₀) + 10) + (P₁ - P₀) := by linarith

/-! ## Internal Popped-Edge Dispatch and Witness Extension -/

private theorem partDjpPopped_internal
    (W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s)
    (hincur₀_ne : ∀ x < n, inCur0 x ≠ cid) (hcont : a.cont ≠ 0)
    (hpop_h : SHHandle) (it₀ : SHItem) (roots₁ : List SHTree) (s₁ : Memory.State)
    (hpop_props : hpop_h.itemBase = a.sh.itemBase ∧ hpop_h.nodeBase = a.sh.nodeBase ∧
      hpop_h.rankThreshold = partRankThreshold ∧ hpop_h.itemCount = a.sh.itemCount)
    (hs1_fr : s₁.frontier = s.frontier)
    (hs1_mod : ∀ x, s₁.mem x ≠ s.mem x →
      InSHPool ic0 nc0 (2 * L.es.length) (4 * L.es.length) a.sh x)
    (hsh1 : SHInv w ic0 nc0 (2 * L.es.length) (4 * L.es.length) hpop_h roots₁ W.created s₁)
    (hperm1 : (it₀ :: forestItems roots₁).Perm (forestItems W.roots))
    (hent1 : ∀ p ∈ forestEntries roots₁, ∃ c₀, (p.1, c₀) ∈ forestEntries W.roots ∧ c₀ ≤ p.2)
    (eIdx : Fin L.es.length) (he_id : it₀.val = eIdx.val)
    (hcu_cid : s₁.mem (L.bufBase + n + (L.es[eIdx.val]'eIdx.isLt).u.val) = cid)
    (hcv_cid : s₁.mem (L.bufBase + n + (L.es[eIdx.val]'eIdx.isLt).v.val) = cid) :
    ∃ W' : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u
        ⟨1, a.hitPrev, a.size, a.tLen, hpop_h⟩ s₁,
      djpPot W' + 4 + 251 ≤ djpPot W + (totalPhi partRankThreshold roots₁ -
        totalPhi partRankThreshold W.roots) ∧ djpRank W' < djpRank W := by
  have hagree_s1 := L.agree_outside_inSHPool W.hib W.hnb hs1_mod
  have hs1_buf : ∀ x, L.bufBase ≤ x → x < L.bufBase + 4 * n → s₁.mem x = s.mem x :=
    fun x hx1 _ => hagree_s1.2 x hx1
  have hu_D := djpWitness_mem_of_inCur_cid W hincur₀_ne _
    ((hs1_buf _ (by omega) (by omega)).symm.trans hcu_cid)
  have hv_D := djpWitness_mem_of_inCur_cid W hincur₀_ne _
    ((hs1_buf _ (by omega) (by omega)).symm.trans hcv_cid)
  have hkeep_s1 : ∀ (e' : Fin L.es.length), ∀ p₀ ∈ forestEntries W.roots, p₀.1.val = e'.val →
      ¬((L.es[e'.val]'e'.isLt).u ∈ W.D.treeVerts W.D.numSteps ∧
        (L.es[e'.val]'e'.isLt).v ∈ W.D.treeVerts W.D.numSteps) →
      ∃ p ∈ forestEntries roots₁, p.1.val = e'.val := fun e' p₀ hp₀ hp₀_id hnot_in =>
    forest_mem_of_pop_ne hperm1 (fun _ hi => hi) he_id hp₀ hp₀_id
      (fun h => hnot_in ⟨h ▸ hu_D, h ▸ hv_D⟩)
  have hrem_eq : remDeg n L.offBase s₁.mem
      (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0) ∪ W.D.treeVerts W.D.numSteps) =
      remDeg n L.offBase s.mem
      (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0) ∪ W.D.treeVerts W.D.numSteps) :=
    remDeg_congr _ fun k _ => hagree_s1.1 (L.offBase + k) (by have := L.csr_lt_itemBase; omega)
  have ⟨hin_in', hin_out'⟩ := djp_inCur_transport (by have := W.hsize; omega)
    hs1_buf W.hincur_in W.hincur_out
  let W' : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u
      ⟨1, a.hitPrev, a.size, a.tLen, hpop_h⟩ s₁ :=
    { roots := roots₁, created := W.created, D := W.D, treeIndexed := W.treeIndexed,
      hfr := hs1_fr.trans W.hfr, hmod := inSHPool_mod_trans W.hib W.hnb W.hmod hs1_mod,
      hib := hpop_props.1.trans W.hib, hnb := hpop_props.2.1.trans W.hnb,
      hrt := hpop_props.2.2.1, hic_ge := hpop_props.2.2.2 ▸ W.hic_ge,
      hic_le := hpop_props.2.2.2 ▸ W.hic_le, hsh := hsh1, hroot := W.hroot,
      hsize := W.hsize, hsize_le := W.hsize_le, htlen := W.htlen, htlen_le := W.htlen_le,
      htlen_dead := W.htlen_dead, htree_len := W.htree_len, htree_w := W.htree_w,
      htree_src := W.htree_src, htree_mem := W.htree_mem.congr fun x hx1 hx2 => hagree_s1.2 x
        (by have := W.htree_len; have := W.htlen; have := W.htlen_le; omega),
      hverts_mem := fun k hk => by
        dsimp only at hk; have := djp_numSteps_add_one_le W.D; have := W.hsize
        exact (hs1_buf _ (by omega) (by omega)).trans (W.hverts_mem k hk),
      hincur_in := hin_in', hincur_out := hin_out',
      hstop_dead := fun x hx hdx => absurd (W.hstop_dead x hx hdx).2.1 hcont,
      hhit_prev := fun hne => absurd (W.hhit_prev hne).2.1 hcont,
      hno_hit := fun h0 => W.hno_hit h0,
      hcap_rem := by rw [hpop_props.2.2.2, hrem_eq]; exact W.hcap_rem,
      hnd_edge := forestItems_nodup_of_perm hperm1 W.hnd_edge,
      hent_prop := hent_prop_lift W hsh1 hent1 (W.D.treeVerts W.D.numSteps) (fun _ h => h),
      hcont_cov := fun _ e' he' hcross => by
        rcases W.hcont_cov hcont e' he' hcross with ⟨p₀, hp₀, hp₀_id⟩
        exact hkeep_s1 e' p₀ hp₀ hp₀_id fun ⟨hu, hv⟩ => (hcross.mp hu) hv,
      hcut_cov := fun e' he' hnot_in hst => by
        rcases W.hcut_cov e' he' hnot_in hst with ⟨p₀, hp₀, hp₀_id⟩
        exact hkeep_s1 e' p₀ hp₀ hp₀_id hnot_in,
      hwpop_fut := fun s_step p hp hcross => by
        rcases hent1 p hp with ⟨c₀, hc₀, hle⟩
        exact (W.hwpop_fut s_step (p.1, c₀) hc₀ hcross).trans hle,
      hempty_stop := fun h0 => absurd h0 Nat.one_ne_zero,
      hcont_size := fun _ => W.hcont_size hcont }
  have hlen_eq : (forestItems W.roots).length = (forestItems roots₁).length + 1 := by
    have hl := hperm1.length_eq; rw [List.length_cons] at hl; omega
  refine ⟨W', ?_, ?_⟩
  · dsimp only [djpPot]; rw [hrem_eq, hpop_props.2.2.2, hlen_eq]
    simp only [Nat.one_ne_zero, ↓reduceIte, hcont, Nat.cast_add, Nat.cast_one]; linarith
  · dsimp only [djpRank, W']; simp only [Nat.one_ne_zero, ↓reduceIte, hcont]
    rw [hpop_props.2.2.2, hlen_eq]; omega

private structure PoppedAddArgs {w n : ℕ} (L : PartLayout w n) (s₀ : Memory.State)
    (dead0 inCur0 edgeState0 : ℕ → ℕ) (cid ic0 nc0 tLen0 : ℕ) (u : Fin n)
    (a : PartDjpState) (s : Memory.State)
    (W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s) where
  hcsr₀ : HoldsUndirCSR L.offBase L.adjBase L.es s₀.mem
  hin₀ : HoldsIndexedEdges L.edgeBase L.es s₀.mem
  hdead₀ : ∀ x < n, s₀.mem (L.bufBase + x) = dead0 x
  hedge₀ : ∀ i < L.es.length, s₀.mem (L.bufBase + 14 * n + i) = edgeState0 i
  hincur₀_ne : ∀ x < n, inCur0 x ≠ cid
  hcid_fit : Fits w cid
  hsimp : ∀ e : Fin L.es.length, (L.es[e.val]'e.isLt).u ≠ (L.es[e.val]'e.isLt).v
  hcont : a.cont ≠ 0
  hhit0 : a.hitPrev = 0
  hpop_h : SHHandle
  it₀ : SHItem
  popKey : ℕ
  roots₁ : List SHTree
  s₁ : Memory.State
  hpop_props : hpop_h.itemBase = a.sh.itemBase ∧ hpop_h.nodeBase = a.sh.nodeBase ∧
    hpop_h.rankThreshold = partRankThreshold ∧ hpop_h.itemCount = a.sh.itemCount
  hs1_fr : s₁.frontier = s.frontier
  hs1_mod : ∀ x, s₁.mem x ≠ s.mem x →
    InSHPool ic0 nc0 (2 * L.es.length) (4 * L.es.length) a.sh x
  hit0_mem : (it₀, popKey) ∈ forestEntries W.roots
  hit0_min : ∀ p ∈ forestEntries W.roots, popKey ≤ p.2
  hsh1 : SHInv w ic0 nc0 (2 * L.es.length) (4 * L.es.length) hpop_h roots₁ W.created s₁
  hperm1 : (it₀ :: forestItems roots₁).Perm (forestItems W.roots)
  hent1 : ∀ p ∈ forestEntries roots₁, ∃ c₀, (p.1, c₀) ∈ forestEntries W.roots ∧ c₀ ≤ p.2
  eIdx : Fin L.es.length
  he_id : it₀.val = eIdx.val
  he_st0 : edgeState0 eIdx.val = 0
  vIn : Fin n
  vOut : Fin n
  hvIn_mem : vIn ∈ W.D.treeVerts W.D.numSteps
  hvOut_not : vOut ∉ W.D.treeVerts W.D.numSteps
  hm_ends : ((L.es[eIdx.val]'eIdx.isLt).u = vIn ∧ (L.es[eIdx.val]'eIdx.isLt).v = vOut) ∨
    ((L.es[eIdx.val]'eIdx.isLt).v = vIn ∧ (L.es[eIdx.val]'eIdx.isLt).u = vOut)
  hew : (L.es[eIdx.val]'eIdx.isLt).weight ≤ popKey
  hfut : ∀ s_step : Fin W.D.numSteps, ((L.es[eIdx.val]'eIdx.isLt).u ∈ W.D.treeVerts s_step.val ↔
    (L.es[eIdx.val]'eIdx.isLt).v ∉ W.D.treeVerts s_step.val) → W.D.wPop s_step ≤ popKey

private abbrev PoppedAddArgs.D'
    {W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s}
    (C : PoppedAddArgs L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s W) :
    DynamicDJPTree n :=
  extendDJP W.D (L.es[C.eIdx.val]'C.eIdx.isLt) C.popKey C.vIn C.vOut C.hew C.hm_ends
    C.hvIn_mem C.hvOut_not C.hfut

private abbrev PoppedAddArgs.s2
    {W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s}
    (C : PoppedAddArgs L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s W) : Memory.State :=
  (Memory.spec 0).clientState C.s₁
    (partCopyIndexedEdge ⟨L.edgeBase, L.bufBase + 10 * n, C.it₀.val, a.tLen⟩)

private abbrev PoppedAddArgs.s3
    {W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s}
    (C : PoppedAddArgs L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s W) : Memory.State :=
  ⟨write3Mem L.bufBase n a.size cid C.vOut.val C.s2.mem, C.s2.frontier⟩

private theorem extendDJP_wpop_fut
    {W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s}
    (C : PoppedAddArgs L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s W)
    (roots' : List SHTree) (hent_r' : ∀ p ∈ forestEntries roots',
      (∃ c₀, (p.1, c₀) ∈ forestEntries C.roots₁ ∧ c₀ ≤ p.2) ∨ ∃ e' : Fin L.es.length,
        p.1.val = e'.val ∧ (((L.es[e'.val]'e'.isLt).u = C.vOut ∧
          (L.es[e'.val]'e'.isLt).v ∉ W.D.treeVerts W.D.numSteps) ∨ ((L.es[e'.val]'e'.isLt).v =
          C.vOut ∧ (L.es[e'.val]'e'.isLt).u ∉ W.D.treeVerts W.D.numSteps))) :
    ∀ s_step : Fin C.D'.numSteps, ∀ p ∈ forestEntries roots',
      (∃ hlt : p.1.val < L.es.length, ((L.es[p.1.val]'hlt).u ∈ C.D'.treeVerts s_step.val ↔
        (L.es[p.1.val]'hlt).v ∉ C.D'.treeVerts s_step.val)) → C.D'.wPop s_step ≤ p.2 := by
  intro s_step p hp ⟨hlt, hcross⟩
  rcases hent_r' p hp with ⟨c₁, hc₁, hle₁⟩ | ⟨e', he'_id, he'_inc⟩
  · rcases C.hent1 (p.1, c₁) hc₁ with ⟨c₀, hc₀, hle₀⟩
    by_cases hs : s_step.val < W.D.numSteps
    · have htv := extendDJP_treeVerts_le W.D (L.es[C.eIdx.val]'C.eIdx.isLt) C.popKey C.vIn C.vOut
        C.hew C.hm_ends C.hvIn_mem C.hvOut_not C.hfut s_step.val hs.le
      rw [show C.D'.wPop s_step = W.D.wPop ⟨s_step.val, hs⟩ by
        simp [PoppedAddArgs.D', extendDJP, hs]]
      exact (W.hwpop_fut ⟨s_step.val, hs⟩ (p.1, c₀) hc₀ ⟨hlt, by simpa [htv] using hcross⟩).trans
        (hle₀.trans hle₁)
    · have hs_eq : s_step.val = W.D.numSteps := by
        have hlt_s := s_step.isLt; simp [PoppedAddArgs.D', extendDJP] at hlt_s; omega
      rw [show C.D'.wPop s_step = C.popKey by simp [PoppedAddArgs.D', extendDJP, hs_eq]]
      exact (C.hit0_min (p.1, c₀) hc₀).trans (hle₀.trans hle₁)
  · exfalso; have he'_eq : L.es[p.1.val]'hlt = (L.es[e'.val]'e'.isLt) := by simp only [he'_id]
    have hmono_s : C.D'.treeVerts s_step.val ⊆ W.D.treeVerts W.D.numSteps := by
      have hs_le : s_step.val ≤ W.D.numSteps := by
        have := s_step.isLt; simp [PoppedAddArgs.D', extendDJP] at this; omega
      dsimp only [PoppedAddArgs.D']; rw [extendDJP_treeVerts_le _ _ _ _ _ _ _ _ _ _ _ hs_le]
      exact fun _ hx => mem_djpVerts_mono W.D.root W.D.vOut hs_le hx
    rcases he'_inc with ⟨hu, hv⟩ | ⟨hv, hu⟩ <;> rw [← he'_eq] at hu hv
    · exact C.hvOut_not (hu ▸ hmono_s (hcross.mpr fun h => hv (hmono_s h)))
    · exact hu (hmono_s (hcross.mpr fun h => C.hvOut_not (hv ▸ hmono_s h)))

private theorem extendDJP_cut_cov
    {W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s}
    (C : PoppedAddArgs L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s W)
    (roots' : List SHTree) (hkeep : ∀ it ∈ forestItems C.roots₁, it ∈ forestItems roots') :
    ∀ e' : Fin L.es.length, edgeState0 e'.val = 0 →
      ¬((L.es[e'.val]'e'.isLt).u ∈ C.D'.treeVerts C.D'.numSteps ∧
        (L.es[e'.val]'e'.isLt).v ∈ C.D'.treeVerts C.D'.numSteps) →
      (∃ s_step : Fin C.D'.numSteps, (L.es[e'.val]'e'.isLt).u ∈ C.D'.treeVerts s_step.val ↔
        (L.es[e'.val]'e'.isLt).v ∉ C.D'.treeVerts s_step.val) →
      ∃ p ∈ forestEntries roots', p.1.val = e'.val := by
  intro e' he' hnot_in ⟨s_step, hcross_s⟩
  have htv_eq : C.D'.treeVerts C.D'.numSteps = insert C.vOut (W.D.treeVerts W.D.numSteps) := by
    dsimp only [PoppedAddArgs.D']; exact extendDJP_treeVerts_succ _ _ _ _ _ _ _ _ _ _
  have hnot_old : ¬((L.es[e'.val]'e'.isLt).u ∈ W.D.treeVerts W.D.numSteps ∧
      (L.es[e'.val]'e'.isLt).v ∈ W.D.treeVerts W.D.numSteps) := fun ⟨hu, hv⟩ =>
    hnot_in ⟨htv_eq ▸ Finset.mem_insert_of_mem hu, htv_eq ▸ Finset.mem_insert_of_mem hv⟩
  have hstep_from_old : ∀ p₀ ∈ forestEntries W.roots, p₀.1.val = e'.val →
      ∃ p ∈ forestEntries roots', p.1.val = e'.val := fun p₀ hp₀ hp₀_id => by
    refine forest_mem_of_pop_ne C.hperm1 hkeep C.he_id hp₀ hp₀_id fun heeq => ?_
    subst heeq; rcases C.hm_ends with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · exact hnot_in ⟨htv_eq ▸ Finset.mem_insert_of_mem (hu ▸ C.hvIn_mem),
        htv_eq ▸ hv ▸ Finset.mem_insert_self _ _⟩
    · exact hnot_in ⟨htv_eq ▸ hu ▸ Finset.mem_insert_self _ _,
        htv_eq ▸ Finset.mem_insert_of_mem (hv ▸ C.hvIn_mem)⟩
  by_cases hs : s_step.val < W.D.numSteps
  · have htv_s := extendDJP_treeVerts_le W.D (L.es[C.eIdx.val]'C.eIdx.isLt) C.popKey C.vIn C.vOut
      C.hew C.hm_ends C.hvIn_mem C.hvOut_not C.hfut s_step.val hs.le
    rcases W.hcut_cov e' he' hnot_old ⟨⟨s_step.val, hs⟩, by simpa [htv_s] using hcross_s⟩ with
      ⟨p₀, hp₀, hp₀_id⟩
    exact hstep_from_old p₀ hp₀ hp₀_id
  · have hs_eq : s_step.val = W.D.numSteps := by
      have hlt_s := s_step.isLt; simp [PoppedAddArgs.D', extendDJP] at hlt_s; omega
    have htv_s : C.D'.treeVerts s_step.val = W.D.treeVerts W.D.numSteps := by
      rw [hs_eq]; dsimp only [PoppedAddArgs.D']
      exact extendDJP_treeVerts_le _ _ _ _ _ _ _ _ _ _ _ le_rfl
    rcases W.hcont_cov C.hcont e' he' (by simpa [htv_s] using hcross_s) with ⟨p₀, hp₀, hp₀_id⟩
    exact hstep_from_old p₀ hp₀ hp₀_id

private structure DjpS3State
    {W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s}
    (C : PoppedAddArgs L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s W) where
  sz1_le_n : a.size + 1 ≤ n
  tlen_lt_n : a.tLen < n
  copy_safe : partCopyIndexedEdgeSafe w ⟨L.edgeBase, L.bufBase + 10 * n, C.it₀.val, a.tLen⟩ C.s₁
  copy_vh : (Memory.spec w).ValidHistory C.s₁ ((Memory.spec w).clientHistory C.s₁
    (partCopyIndexedEdge ⟨L.edgeBase, L.bufBase + 10 * n, C.it₀.val, a.tLen⟩))
  copy_cost : memoryCost
    (partCopyIndexedEdge ⟨L.edgeBase, L.bufBase + 10 * n, C.it₀.val, a.tLen⟩) C.s₁ ≤ 8
  s2_fr : C.s2.frontier = L.bufBase + (14 * n + 14 * L.es.length)
  dout_eq : C.s2.mem (L.bufBase + C.vOut.val) = dead0 C.vOut.val
  s2_mod : ∀ x, ¬(L.bufBase + 10 * n + 4 * a.tLen ≤ x ∧
    x < L.bufBase + 10 * n + 4 * a.tLen + 4) → C.s2.mem x = C.s₁.mem x
  s3_fr : C.s3.frontier = L.bufBase + (14 * n + 14 * L.es.length)
  s3_sh : SHInv w ic0 nc0 (2 * L.es.length) (4 * L.es.length) C.hpop_h C.roots₁ W.created C.s3
  hin3 : HoldsIndexedEdges L.edgeBase L.es C.s3.mem
  hcsr3 : HoldsUndirCSR L.offBase L.adjBase L.es C.s3.mem
  s3_edgeState : ∀ i < L.es.length, C.s3.mem (L.bufBase + 14 * n + i) = edgeState0 i
  s3_mod_s0 : ∀ x, C.s3.mem x ≠ s₀.mem x → DjpModRange L ic0 nc0 tLen0 (a.tLen + 1) x
  s3_tree : HoldsIndexedEdges (L.bufBase + 10 * n + 4 * tLen0)
    (W.treeIndexed ++ [L.es[C.eIdx.val]'C.eIdx.isLt]) C.s3.mem
  s3_verts : ∀ k (hk : k < a.size + 1), C.s3.mem (L.bufBase + 3 * n + k) =
    ((djpVertsList C.D')[k]'(by
      rw [djpVertsList_length]; dsimp only [PoppedAddArgs.D', extendDJP]
      have := W.hsize; omega)).val
  s3_incur_in : ∀ x : Fin n, x ∈ C.D'.treeVerts C.D'.numSteps →
    C.s3.mem (L.bufBase + n + x.val) = cid ∧ ∃ k < a.size + 1,
      C.s3.mem (L.bufBase + 3 * n + k) = x.val ∧ C.s3.mem (L.bufBase + 2 * n + x.val) = k
  s3_incur_out : ∀ x : Fin n, x ∉ C.D'.treeVerts C.D'.numSteps →
    C.s3.mem (L.bufBase + n + x.val) = inCur0 x.val
  s3_rem_eq : remDeg n L.offBase C.s3.mem
      (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0) ∪ W.D.treeVerts W.D.numSteps) =
    remDeg n L.offBase s.mem
      (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0) ∪ W.D.treeVerts W.D.numSteps)
  s3_rem_anti : remDeg n L.offBase C.s3.mem
      (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0) ∪ C.D'.treeVerts C.D'.numSteps) ≤
    remDeg n L.offBase s.mem
      (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0) ∪ W.D.treeVerts W.D.numSteps)

/-- Appends two contiguous stride-4 `HoldsIndexedEdges` regions. -/
theorem holdsIndexedEdges_append {n : ℕ} {base : ℕ} {xs ys : List (IndexedEdge n)}
    {mem : ℕ → ℕ} (hx : HoldsIndexedEdges base xs mem)
    (hy : HoldsIndexedEdges (base + 4 * xs.length) ys mem) :
    HoldsIndexedEdges base (xs ++ ys) mem := by
  intro i hi
  by_cases hlt : i < xs.length
  · simpa [List.getElem_append_left hlt] using hx i hlt
  · have hge : xs.length ≤ i := Nat.le_of_not_lt hlt
    have hlt2 : i - xs.length < ys.length := by rw [List.length_append] at hi; omega
    simpa [List.getElem_append_right hge, show base + 4 * xs.length + 4 * (i - xs.length) =
      base + 4 * i by omega] using hy (i - xs.length) hlt2

private theorem partDjpAddVert_s3_state
    {W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s}
    (C : PoppedAddArgs L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s W) : DjpS3State C := by
  let m := L.es.length; let s₁ := C.s₁; let s₂ := C.s2; let s₃ := C.s3; let D' := C.D'
  let deadSet : Finset (Fin n) := Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)
  have htv_eq : D'.treeVerts D'.numSteps = insert C.vOut (W.D.treeVerts W.D.numSteps) := by
    dsimp only [D', PoppedAddArgs.D']; exact extendDJP_treeVerts_succ _ _ _ _ _ _ _ _ _ _
  have h16 := L.h16; have hn_pos := L.hn_pos; have hwf1 := C.hsh1.wf
  have hagree_s1 := L.agree_outside_inSHPool W.hib W.hnb C.hs1_mod
  have hs1_buf : ∀ x, L.bufBase ≤ x → x < L.bufBase + (14 * n + 14 * m) → s₁.mem x = s.mem x :=
    fun x hx1 _ => hagree_s1.2 x hx1
  have hin1 := (L.congr_below_itemBase hagree_s1.1).1 (djpWitness_edges W C.hin₀)
  have hcsr1 := (L.congr_below_itemBase hagree_s1.1).2 (djpWitness_csr W C.hcsr₀)
  have ha_sz1_le_n : a.size + 1 ≤ n := by
    have hle := (Finset.card_le_univ (D'.treeVerts D'.numSteps)).trans_eq (Fintype.card_fin n)
    rw [djpVerts_card D' D'.numSteps le_rfl] at hle
    have := W.hsize; dsimp only [D', PoppedAddArgs.D', extendDJP] at hle; omega
  have htlen_lt_n : a.tLen < n := by
    have hdisj : Disjoint deadSet (W.D.treeVerts W.D.numSteps) := Finset.disjoint_left.mpr
      fun x hxd hxt => (Finset.mem_filter.mp hxd).2 (W.hno_hit C.hhit0 x hxt)
    have hcu := Finset.card_union_of_disjoint hdisj
    dsimp only [deadSet] at hcu
    rw [djpVerts_card W.D W.D.numSteps le_rfl] at hcu
    have hle := (Finset.card_le_univ (deadSet ∪ W.D.treeVerts W.D.numSteps)).trans_eq
      (Fintype.card_fin n)
    dsimp only [deadSet] at hcu hle
    have := W.htlen_dead; omega
  rcases partCopyIndexedEdge_spec h16 hwf1 (srcBase := L.edgeBase)
      (dstBase := L.bufBase + 10 * n) (srcIdx := C.it₀.val) (dstIdx := a.tLen)
      (by have := L.edge_lt_itemBase; have := L.hit_nd; have := L.hnd_buf
          rw [C.hs1_fr, W.hfr, C.he_id]; omega)
      (by rw [C.hs1_fr, W.hfr]; omega) with
    ⟨hcopy_safe, hcopy_vh, hcopy_cost, hs2_fr, hwf2, hs2_mod, hc0, hc1, hc2, hc3⟩
  have hfr2 : s₂.frontier = L.bufBase + (14 * n + 14 * m) := hs2_fr.trans (C.hs1_fr.trans W.hfr)
  have hdout_eq : s₂.mem (L.bufBase + C.vOut.val) = dead0 C.vOut.val := by
    rw [hs2_mod _ (by omega)]
    exact (hs1_buf _ (by omega) (by omega)).trans (djpWitness_dead W C.hdead₀ _ C.vOut.isLt)
  have hwf3 : Memory.WellFormed w s₃ := write3Mem_wf hwf2
    (L.hfit_end.of_le (by have := C.vOut.isLt; omega)) C.hcid_fit
    (L.hfit_end.of_le (by have := ha_sz1_le_n; omega))
  have hs3_below : ∀ x < L.itemBase, s₃.mem x = s₁.mem x := fun x hx => by
    have := L.hit_nd; have := L.hnd_buf
    exact (write3Mem_agree_outside (by omega) (by omega) (by omega)).trans (hs2_mod x (by omega))
  have hs3_sh : SHInv w ic0 nc0 (2 * m) (4 * m) C.hpop_h C.roots₁ W.created s₃ :=
    C.hsh1.congr_outside hwf3 hs2_fr fun a' ha' => by
      rcases L.inSHPool_lt_bufBase (C.hpop_props.1.trans W.hib) (C.hpop_props.2.1.trans W.hnb) ha'
        with ⟨h1, h2⟩
      exact (write3Mem_agree_outside (by omega) (by omega) (by omega)).trans
        (hs2_mod a' (by omega))
  have hs3_tree : HoldsIndexedEdges (L.bufBase + 10 * n + 4 * tLen0)
      (W.treeIndexed ++ [L.es[C.eIdx.val]'C.eIdx.isLt]) s₃.mem := by
    refine holdsIndexedEdges_append (W.htree_mem.congr fun x hx1 hx2 => by
      rw [W.htree_len] at hx2
      exact (write3Mem_agree_outside (bufBase := L.bufBase) (n := n) (size := a.size) (cid := cid)
        (v := C.vOut.val) (x := x) (mem := s₂.mem) (by omega) (by omega) (by omega)).trans
        ((hs2_mod x (by have := W.htlen; omega)).trans
          (hs1_buf x (by omega) (by have := W.htlen; have := W.htlen_le; omega)))) fun i hi => by
      have hi0 := Nat.lt_one_iff.mp hi; subst hi0
      have hbase : L.bufBase + 10 * n + 4 * tLen0 + 4 * W.treeIndexed.length =
          L.bufBase + 10 * n + 4 * a.tLen := by have := W.htree_len; have := W.htlen; omega
      have hed := hin1 C.eIdx.val C.eIdx.isLt
      have hc : ∀ j < 4, s₃.mem (L.bufBase + 10 * n + 4 * a.tLen + j) =
          s₂.mem (L.bufBase + 10 * n + 4 * a.tLen + j) := fun j hj =>
        write3Mem_agree_outside (by omega) (by omega) (by omega)
      simp only [hbase, List.getElem_singleton, Nat.mul_zero, Nat.add_zero]
      rw [show s₃.mem (L.bufBase + 10 * n + 4 * a.tLen) = s₂.mem (L.bufBase + 10 * n + 4 * a.tLen)
          by simpa using hc 0 (by omega), hc 1 (by omega), hc 2 (by omega), hc 3 (by omega),
        hc0, hc1, hc2, hc3, C.he_id]
      exact ⟨hed.1, hed.2.1, hed.2.2.1, hed.2.2.2⟩
  have hs2_incur := djp_inCur_transport (by have := W.hsize; omega)
    (fun x hx1 hx2 => (hs2_mod x (by omega)).trans (hs1_buf x hx1 (by omega)))
    W.hincur_in W.hincur_out
  have ⟨hs3_in, hs3_out⟩ := write3Mem_incur (mem := s₂.mem) C.hvOut_not (by omega)
    hs2_incur.1 hs2_incur.2
  have hs3_rem_eq : remDeg n L.offBase s₃.mem (deadSet ∪ W.D.treeVerts W.D.numSteps) =
      remDeg n L.offBase s.mem (deadSet ∪ W.D.treeVerts W.D.numSteps) :=
    remDeg_congr _ fun k _ => (hs3_below (L.offBase + k)
      (by have := L.csr_lt_itemBase; omega)).trans
      (hagree_s1.1 (L.offBase + k) (by have := L.csr_lt_itemBase; omega))
  exact {
    sz1_le_n := ha_sz1_le_n, tlen_lt_n := htlen_lt_n, copy_safe := hcopy_safe,
    copy_vh := hcopy_vh, copy_cost := hcopy_cost, s2_fr := hfr2, dout_eq := hdout_eq,
    s2_mod := hs2_mod, s3_fr := hfr2, s3_sh := hs3_sh,
    hin3 := (L.congr_below_itemBase hs3_below).1 hin1,
    hcsr3 := (L.congr_below_itemBase hs3_below).2 hcsr1,
    s3_edgeState := fun i hi => (write3Mem_agree_outside (by omega) (by omega) (by omega)).trans
      ((hs2_mod _ (by omega)).trans ((hs1_buf _ (by omega) (by omega)).trans
        (djpWitness_edgeState W C.hedge₀ i hi))),
    s3_mod_s0 := fun x hne => by
      by_cases hw3 : write3Mem L.bufBase n a.size cid C.vOut.val s₂.mem x ≠ s₂.mem x
      · exact .inr (.inl (write3Mem_in_range C.vOut.isLt (by omega) hw3))
      · by_cases hs2d : s₂.mem x ≠ s₁.mem x
        · refine .inr (.inr ?_); have := W.htlen
          by_contra hnot; exact hs2d (hs2_mod x fun ⟨h1, h2⟩ => hnot ⟨by omega, by omega⟩)
        · by_cases hs1d : s₁.mem x ≠ s.mem x
          · exact .inl (by simpa only [InSHPool, W.hib, W.hnb] using C.hs1_mod x hs1d)
          · have hxw : s.mem x ≠ s₀.mem x := fun h => hne (by
              rw [show s₃.mem x = s₂.mem x from not_not.mp hw3, not_not.mp hs2d, not_not.mp hs1d]
              exact h)
            rcases W.hmod x hxw with h | h | ⟨h1, h2⟩
            · exact .inl h
            · exact .inr (.inl h)
            · exact .inr (.inr ⟨h1, by have := W.htlen; omega⟩),
    s3_tree := hs3_tree,
    s3_verts := fun k hk => by
      by_cases hkeq : k = a.size
      · subst hkeq
        have hvs : s₃.mem (L.bufBase + 3 * n + a.size) = C.vOut.val := by
          dsimp only [s₃, write3Mem]; rw [Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_self]
        have hlen' : a.size < (djpVertsList D').length := by
          rw [djpVertsList_length]; dsimp only [D', PoppedAddArgs.D', extendDJP]
          have := W.hsize; omega
        rw [hvs, show (djpVertsList D')[a.size]'hlen' =
            D'.vOut ⟨W.D.numSteps, Nat.lt_succ_self _⟩ by
          simp only [W.hsize]
          exact djpVertsList_getElem_succ D' ⟨W.D.numSteps, Nat.lt_succ_self _⟩]
        simp [D', PoppedAddArgs.D', extendDJP]
      · have hag : s₃.mem (L.bufBase + 3 * n + k) = s.mem (L.bufBase + 3 * n + k) :=
          (write3Mem_agree_outside (by omega) (by omega) (by omega)).trans
            ((hs2_mod _ (by omega)).trans (hs1_buf _ (by omega) (by omega)))
        rw [hag, W.hverts_mem k (by omega)]
        refine congrArg Fin.val ?_
        rcases k with _ | j
        · simp [djpVertsList, PoppedAddArgs.D', extendDJP, W.hroot]
        · have hj_w : j < W.D.numSteps := by have := W.hsize; omega
          have hL := djpVertsList_getElem_succ W.D ⟨j, hj_w⟩
          have hR := djpVertsList_getElem_succ C.D'
            ⟨j, by dsimp only [PoppedAddArgs.D', extendDJP]; omega⟩
          exact hL.trans (Eq.trans (by simp [PoppedAddArgs.D', extendDJP, hj_w]) hR.symm),
    s3_incur_in := fun x hx => hs3_in x (htv_eq ▸ hx),
    s3_incur_out := fun x hx => hs3_out x (htv_eq ▸ hx), s3_rem_eq := hs3_rem_eq,
    s3_rem_anti := by
      rw [← hs3_rem_eq]; exact remDeg_anti fun x hx => (Finset.mem_union.mp hx).elim
        (Finset.mem_union_left _) fun h => Finset.mem_union_right _
          (htv_eq ▸ Finset.mem_insert_of_mem h) }

private theorem partDjpPopped_addVert_finish
    {W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s}
    (C : PoppedAddArgs L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s W) (S3 : DjpS3State C)
    (cont' hit' : ℕ) (h' : SHHandle) (roots' : List SHTree) (created' : ℕ → ℕ) (s' : Memory.State)
    (hme : let me := partDjpMaybeExpand ⟨L.toEnv, cid, C.hpop_h, C.vOut.val, dead0 C.vOut.val,
        a.size + 1, a.tLen + 1⟩
      partDjpMaybeExpandSafe w ⟨L.toEnv, cid, C.hpop_h, C.vOut.val, dead0 C.vOut.val,
        a.size + 1, a.tLen + 1⟩ C.s3 ∧
      (Memory.spec w).ValidHistory C.s3 ((Memory.spec w).clientHistory C.s3 me) ∧
      (Memory.spec 0).clientResult C.s3 me = ⟨cont', hit', a.size + 1, a.tLen + 1, h'⟩ ∧
      (Memory.spec 0).clientState C.s3 me = s')
    (hs'_fr : s'.frontier = L.bufBase + (14 * n + 14 * L.es.length))
    (hs'_mod_s3 : ∀ x, s'.mem x ≠ C.s3.mem x →
      InSHPool ic0 nc0 (2 * L.es.length) (4 * L.es.length) C.hpop_h x)
    (hh' : h'.itemBase = L.itemBase ∧ h'.nodeBase = L.nodeBase ∧
      h'.rankThreshold = partRankThreshold ∧ ic0 ≤ h'.itemCount)
    (hsh' : SHInv w ic0 nc0 (2 * L.es.length) (4 * L.es.length) h' roots' created' s')
    (hstop_cond : (cont' = 0 ∧ hit' = 1 ∧ dead0 C.vOut.val ≠ 0) ∨
      (cont' = 0 ∧ hit' = 0 ∧ dead0 C.vOut.val = 0 ∧ L.maxsize ≤ a.size + 1) ∨
      (cont' = 1 ∧ hit' = 0 ∧ dead0 C.vOut.val = 0 ∧ a.size + 1 < L.maxsize))
    (hcap_rem' : h'.itemCount + remDeg n L.offBase s'.mem
      (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0) ∪ C.D'.treeVerts C.D'.numSteps) ≤
      2 * L.es.length)
    (hnd' : ((forestItems roots').map SHItem.val).Nodup)
    (hkeep' : ∀ it ∈ forestItems C.roots₁, it ∈ forestItems roots')
    (hent_r' : ∀ p ∈ forestEntries roots', (∃ c₀, (p.1, c₀) ∈ forestEntries C.roots₁ ∧ c₀ ≤ p.2) ∨
      ∃ e' : Fin L.es.length, p.1.val = e'.val ∧
        (((L.es[e'.val]'e'.isLt).u = C.vOut ∧
          (L.es[e'.val]'e'.isLt).v ∉ W.D.treeVerts W.D.numSteps) ∨ ((L.es[e'.val]'e'.isLt).v =
          C.vOut ∧ (L.es[e'.val]'e'.isLt).u ∉ W.D.treeVerts W.D.numSteps)))
    (hent_prop' : ∀ p ∈ forestEntries roots', ∃ e' : Fin L.es.length, p.1.val = e'.val ∧
      p.1.origKey = (L.es[e'.val]'e'.isLt).weight ∧ p.1.origKey ≤ p.2 ∧ edgeState0 e'.val = 0 ∧
      ((L.es[e'.val]'e'.isLt).u ∈ C.D'.treeVerts C.D'.numSteps ∨
       (L.es[e'.val]'e'.isLt).v ∈ C.D'.treeVerts C.D'.numSteps))
    (hcont_cov' : cont' ≠ 0 → ∀ e' : Fin L.es.length, edgeState0 e'.val = 0 →
      ((L.es[e'.val]'e'.isLt).u ∈ C.D'.treeVerts C.D'.numSteps ↔
        (L.es[e'.val]'e'.isLt).v ∉ C.D'.treeVerts C.D'.numSteps) →
      ∃ p ∈ forestEntries roots', p.1.val = e'.val)
    (hpot_of : ∀ W' : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u
        ⟨cont', hit', a.size + 1, a.tLen + 1, h'⟩ s', W'.D = C.D' → W'.roots = roots' →
      let d : PartDjpAddVertArgs := ⟨L.toEnv, cid, C.hpop_h, C.it₀.val, C.vOut.val, a.size, a.tLen⟩
      memoryCost (partDjpAddVert d) C.s₁ = memoryCost (partCopyIndexedEdge
        ⟨L.edgeBase, L.bufBase + 10 * n, C.it₀.val, a.tLen⟩) C.s₁ + 4 +
        memoryCost (partDjpMaybeExpand ⟨L.toEnv, cid, C.hpop_h, C.vOut.val, dead0 C.vOut.val,
          a.size + 1, a.tLen + 1⟩) C.s3 →
      djpPot W' + (memoryCost (partDjpAddVert d) C.s₁ : ℚ) + (4 + 251) ≤
        djpPot W + (totalPhi partRankThreshold C.roots₁ - totalPhi partRankThreshold W.roots) ∧
      djpRank W' < djpRank W) :
    let d : PartDjpAddVertArgs := ⟨L.toEnv, cid, C.hpop_h, C.it₀.val, C.vOut.val, a.size, a.tLen⟩
    DjpStepPost W (partDjpAddVert d) partDjpAddVertSafe d C.s₁ (4 + 251) C.roots₁ := by
  let d : PartDjpAddVertArgs := ⟨L.toEnv, cid, C.hpop_h, C.it₀.val, C.vOut.val, a.size, a.tLen⟩
  let copyP := partCopyIndexedEdge ⟨L.edgeBase, L.bufBase + 10 * n, C.it₀.val, a.tLen⟩
  let me := partDjpMaybeExpand ⟨L.toEnv, cid, C.hpop_h, C.vOut.val, dead0 C.vOut.val,
    a.size + 1, a.tLen + 1⟩
  have htlen_lt_n := S3.tlen_lt_n; have hsize_lt_max := W.hcont_size C.hcont
  have hdout := S3.dout_eq; have hfr2 := S3.s2_fr
  have hvOut_fit : Fits w C.vOut.val := L.hfit_end.of_le (by have := C.vOut.isLt; omega)
  have hsz_fit : Fits w a.size := L.hfit_end.of_le (by have := S3.sz1_le_n; omega)
  have hvh_of : (Memory.spec w).ValidHistory C.s3 ((Memory.spec w).clientHistory C.s3 me) →
      (Memory.spec w).ValidHistory C.s₁
        ((Memory.spec w).clientHistory C.s₁ (partDjpAddVert d)) := by
    intro hm; rw [partDjpAddVert_def]; dsimp only [d, PartLayout.toEnv]
    refine validHistory_bind_step S3.copy_vh (validHistory_read_bind (by rw [hfr2]; omega)
      (validHistory_write_bind (by have := S3.sz1_le_n; rw [hfr2]; omega) hvOut_fit
        (validHistory_write_bind (by dsimp only; rw [hfr2]; omega) C.hcid_fit
          (validHistory_write_bind (by dsimp only; rw [hfr2]; omega) hsz_fit (by
            change (Memory.spec w).ValidHistory C.s3 ((Memory.spec w).clientHistory C.s3
              (partDjpMaybeExpand ⟨L.toEnv, cid, C.hpop_h, C.vOut.val,
                C.s2.mem (L.bufBase + C.vOut.val), a.size + 1, a.tLen + 1⟩))
            rw [hdout]; exact hm)))))
  have hres_eq : (Memory.spec 0).clientResult C.s₁ (partDjpAddVert d) =
      ⟨cont', hit', a.size + 1, a.tLen + 1, h'⟩ := by
    rw [partDjpAddVert_def]; dsimp only [d, PartLayout.toEnv]
    rw [StateTransitionSpec.clientResult_bind, clientResult_bind_read, clientResult_bind_write,
      clientResult_bind_write, clientResult_bind_write]
    change (Memory.spec 0).clientResult C.s3 (partDjpMaybeExpand ⟨L.toEnv, cid, C.hpop_h,
      C.vOut.val, C.s2.mem (L.bufBase + C.vOut.val), a.size + 1, a.tLen + 1⟩) = _
    rw [hdout]; exact hme.2.2.1
  have hs_eq : (Memory.spec 0).clientState C.s₁ (partDjpAddVert d) = s' := by
    rw [partDjpAddVert_def]; dsimp only [d, PartLayout.toEnv]
    rw [StateTransitionSpec.clientState_bind, clientState_bind_read, clientState_bind_write,
      clientState_bind_write, clientState_bind_write]
    change (Memory.spec 0).clientState C.s3 (partDjpMaybeExpand ⟨L.toEnv, cid, C.hpop_h,
      C.vOut.val, C.s2.mem (L.bufBase + C.vOut.val), a.size + 1, a.tLen + 1⟩) = _
    rw [hdout]; exact hme.2.2.2
  have hcost_eq : memoryCost (partDjpAddVert d) C.s₁ = memoryCost copyP C.s₁ + 4 +
      memoryCost me C.s3 := by
    rw [partDjpAddVert_def]; dsimp only [d, PartLayout.toEnv]
    rw [memoryCost_bind', memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_write, clientState_write, memoryCost_bind', memoryCost_write,
      clientState_write, memoryCost_bind', memoryCost_write, clientState_write]
    change _ + (1 + (1 + (1 + (1 + memoryCost (partDjpMaybeExpand ⟨L.toEnv, cid, C.hpop_h,
      C.vOut.val, C.s2.mem (L.bufBase + C.vOut.val), a.size + 1, a.tLen + 1⟩) C.s3)))) = _
    rw [hdout]; dsimp only [copyP, me, PartLayout.toEnv]; omega
  have hagree_exp := L.agree_outside_inSHPool (C.hpop_props.1.trans W.hib)
    (C.hpop_props.2.1.trans W.hnb) hs'_mod_s3
  have hs'_buf : ∀ x, L.bufBase ≤ x → x < L.bufBase + 4 * n → s'.mem x = C.s3.mem x :=
    fun x hx1 _ => hagree_exp.2 x hx1
  have ⟨hin_in', hin_out'⟩ := djp_inCur_transport
    (by change a.size + 1 ≤ W.D.numSteps + 1 + 1; have := W.hsize; omega)
    hs'_buf S3.s3_incur_in S3.s3_incur_out
  have htv_eq : C.D'.treeVerts C.D'.numSteps = insert C.vOut (W.D.treeVerts W.D.numSteps) := by
    dsimp only [PoppedAddArgs.D']; exact extendDJP_treeVerts_succ _ _ _ _ _ _ _ _ _ _
  let W' : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u
      ⟨cont', hit', a.size + 1, a.tLen + 1, h'⟩ s' :=
    { roots := roots', created := created', D := C.D',
      treeIndexed := W.treeIndexed ++ [L.es[C.eIdx.val]'C.eIdx.isLt], hfr := hs'_fr,
      hmod := inSHPool_mod_trans (C.hpop_props.1.trans W.hib) (C.hpop_props.2.1.trans W.hnb)
        S3.s3_mod_s0 hs'_mod_s3,
      hib := hh'.1, hnb := hh'.2.1, hrt := hh'.2.2.1, hic_ge := hh'.2.2.2,
      hic_le := hsh'.ic_max, hsh := hsh', hroot := W.hroot,
      hsize := by change a.size + 1 = (W.D.numSteps + 1) + 1; have := W.hsize; omega,
      hsize_le := by change a.size + 1 ≤ L.maxsize; omega,
      htlen := by change a.tLen + 1 = tLen0 + (W.D.numSteps + 1); have := W.htlen; omega,
      htlen_le := by change a.tLen + 1 ≤ n; omega,
      htlen_dead := by change a.tLen + 1 ≤ _ + (W.D.numSteps + 1); have := W.htlen_dead; omega,
      htree_len := by rw [List.length_append, List.length_singleton, W.htree_len]; rfl,
      htree_w := by
        rw [List.map_append, List.map_singleton, W.htree_w]; dsimp only [PoppedAddArgs.D']
        exact (extendDJP_treeEdges _ _ _ _ _ _ _ _ _ _).symm,
      htree_src := fun e he => (List.mem_append.mp he).elim (W.htree_src e) fun h2 =>
        ⟨C.eIdx, List.mem_singleton.mp h2, C.he_st0⟩,
      htree_mem := S3.s3_tree.congr fun x hx1 hx2 => hagree_exp.2 x (by
        rw [List.length_append, List.length_singleton, W.htree_len] at hx2
        have := W.htlen; omega),
      hverts_mem := fun k hk => by
        dsimp only at hk; have := W.hsize; have := S3.sz1_le_n
        exact (hs'_buf _ (by omega) (by omega)).trans (S3.s3_verts k hk),
      hincur_in := hin_in', hincur_out := hin_out',
      hstop_dead := fun x hx hdx => by
        rcases Finset.mem_insert.mp (htv_eq ▸ hx) with rfl | hx_old
        · rcases hstop_cond with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, hd0', _⟩ | ⟨rfl, rfl, hd0', _⟩
          · exact ⟨rfl, rfl, by simp [PoppedAddArgs.D', extendDJP],
              fun _ => by simp [PoppedAddArgs.D', extendDJP]⟩
          · exact absurd hd0' hdx
          · exact absurd hd0' hdx
        · exact absurd (W.hno_hit C.hhit0 x hx_old) hdx,
      hhit_prev := fun hne => by
        rcases hstop_cond with ⟨rfl, rfl, hd_ne⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
        · exact ⟨rfl, rfl, by simp [PoppedAddArgs.D', extendDJP],
            fun _ => by simp [PoppedAddArgs.D', extendDJP, hd_ne]⟩
        · exact absurd rfl hne
        · exact absurd rfl hne,
      hno_hit := fun h0 x hx => by
        rcases Finset.mem_insert.mp (htv_eq ▸ hx) with rfl | hx_old
        · rcases hstop_cond with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, hd0', _⟩ | ⟨rfl, rfl, hd0', _⟩
          · exact absurd h0 Nat.one_ne_zero
          · exact hd0'
          · exact hd0'
        · exact W.hno_hit C.hhit0 x hx_old,
      hcap_rem := hcap_rem', hnd_edge := hnd', hent_prop := hent_prop', hcont_cov := hcont_cov',
      hcut_cov := extendDJP_cut_cov C roots' hkeep',
      hwpop_fut := extendDJP_wpop_fut C roots' hent_r',
      hempty_stop := fun hcont0 hhit0' hlt_max => by
        rcases hstop_cond with ⟨_, rfl, _⟩ | ⟨_, _, _, hmax⟩ | ⟨rfl, _⟩
        · exact absurd hhit0' Nat.one_ne_zero
        · exact absurd hmax (not_le_of_gt hlt_max)
        · exact absurd hcont0 Nat.one_ne_zero,
      hcont_size := fun hne => by
        rcases hstop_cond with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨_, _, _, hlt⟩ <;>
          first | exact absurd rfl hne | exact hlt }
  refine ⟨by
      rw [partDjpAddVertSafe_def]; dsimp only [d, PartLayout.toEnv]
      refine ⟨L.h16, L.hfit_end.of_le (by have := S3.sz1_le_n; omega),
        L.hfit_end.of_le (by have := S3.tlen_lt_n; omega), L.hfit_end.of_le (by omega),
        S3.copy_safe, by rw [C.hs1_fr, W.hfr]; have := C.vOut.isLt; omega,
        by rw [C.hs1_fr, W.hfr]; have := S3.sz1_le_n; omega,
        by rw [C.hs1_fr, W.hfr]; have := C.vOut.isLt; omega,
        by rw [C.hs1_fr, W.hfr]; have := C.vOut.isLt; omega, ?_⟩
      change partDjpMaybeExpandSafe w ⟨L.toEnv, cid, C.hpop_h, C.vOut.val,
        C.s2.mem (L.bufBase + C.vOut.val), a.size + 1, a.tLen + 1⟩ C.s3
      rw [hdout]; exact hme.1,
    hvh_of hme.2.1, by rw [hs_eq, hs'_fr, W.hfr], fun x hx => by
      rw [hs_eq]; by_cases hdiff : s'.mem x = C.s3.mem x
      · rw [hdiff]; have := S3.sz1_le_n; have := C.vOut.isLt; have := W.htlen
        exact (write3Mem_agree_outside (by omega) (by omega) (by omega)).trans
          (S3.s2_mod x fun ⟨h1, h2⟩ => hx (.inr (.inr ⟨by omega, by omega⟩)))
      · exfalso; exact hx (.inl (by
          simpa only [InSHPool, C.hpop_props.1, C.hpop_props.2.1, W.hib, W.hnb] using
            hs'_mod_s3 x hdiff)),
    by rw [hres_eq, hs_eq]; exact ⟨W', hpot_of W' rfl rfl hcost_eq⟩⟩

private theorem partDjpPopped_addVert_spec
    {W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s}
    (C : PoppedAddArgs L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s W) :
    let d : PartDjpAddVertArgs := ⟨L.toEnv, cid, C.hpop_h, C.it₀.val, C.vOut.val, a.size, a.tLen⟩
    DjpStepPost W (partDjpAddVert d) partDjpAddVertSafe d C.s₁ (4 + 251) C.roots₁ := by
  let m := L.es.length; let deadSet : Finset (Fin n) := Finset.univ.filter fun x : Fin n =>
    dead0 x.val ≠ 0
  have h16 := L.h16; have hsize_lt_max : a.size < L.maxsize := W.hcont_size C.hcont
  have htv_eq : C.D'.treeVerts C.D'.numSteps = insert C.vOut (W.D.treeVerts W.D.numSteps) := by
    dsimp only [PoppedAddArgs.D']; exact extendDJP_treeVerts_succ _ _ _ _ _ _ _ _ _ _
  have S3 := partDjpAddVert_s3_state C
  have hrem_d0 : remDeg n L.offBase s.mem (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0) ∪
      W.D.treeVerts W.D.numSteps) =
      remDeg n L.offBase s.mem (deadSet ∪ W.D.treeVerts W.D.numSteps) := rfl
  have hlen_w : (forestItems W.roots).length = (forestItems C.roots₁).length + 1 := by
    have hl := C.hperm1.length_eq; rw [List.length_cons] at hl; omega
  have hnd1 := forestItems_nodup_of_perm C.hperm1 W.hnd_edge
  have hent_prop1 := hent_prop_lift W C.hsh1 C.hent1 (C.D'.treeVerts C.D'.numSteps) fun _ hx =>
    htv_eq ▸ Finset.mem_insert_of_mem hx
  have hstop_post : ∀ (hit' : ℕ) (hcond : (hit' = 1 ∧ dead0 C.vOut.val ≠ 0) ∨
        (hit' = 0 ∧ dead0 C.vOut.val = 0 ∧ L.maxsize ≤ a.size + 1)),
      let d : PartDjpAddVertArgs := ⟨L.toEnv, cid, C.hpop_h, C.it₀.val, C.vOut.val, a.size, a.tLen⟩
      DjpStepPost W (partDjpAddVert d)
        partDjpAddVertSafe ⟨L.toEnv, cid, C.hpop_h, C.it₀.val, C.vOut.val, a.size, a.tLen⟩
        C.s₁ (4 + 251) C.roots₁ := by
    intro hit' hcond
    have hsc : (0 = 0 ∧ hit' = 1 ∧ dead0 C.vOut.val ≠ 0) ∨
        (0 = 0 ∧ hit' = 0 ∧ dead0 C.vOut.val = 0 ∧ L.maxsize ≤ a.size + 1) ∨
        (0 = 1 ∧ hit' = 0 ∧ dead0 C.vOut.val = 0 ∧ a.size + 1 < L.maxsize) :=
      hcond.elim (fun ⟨h1, h2⟩ => .inl ⟨rfl, h1, h2⟩)
        (fun ⟨h1, h2, h3⟩ => .inr (.inl ⟨rfl, h1, h2, h3⟩))
    have hprog_me : partDjpMaybeExpand ⟨L.toEnv, cid, C.hpop_h, C.vOut.val, dead0 C.vOut.val,
        a.size + 1, a.tLen + 1⟩ = pure ⟨0, hit', a.size + 1, a.tLen + 1, C.hpop_h⟩ := by
      rw [partDjpMaybeExpand_def]
      rcases hcond with ⟨rfl, hd_ne⟩ | ⟨rfl, hd0_eq, hmax_le⟩
      · rw [ite_eq_left hd_ne]
      · rw [ite_eq_right (not_not.mpr hd0_eq),
          ite_eq_left (by dsimp only [PartLayout.toEnv]; exact hmax_le)]
    refine partDjpPopped_addVert_finish C S3 0 hit' C.hpop_h C.roots₁ W.created C.s3
      ⟨by rw [partDjpMaybeExpandSafe_def]; exact ⟨h16, fun hd0_eq hnot_le =>
          hcond.elim (fun h => absurd hd0_eq h.2) (fun h => absurd h.2.2 hnot_le)⟩,
        by rw [hprog_me]; exact validHistory_pure w _ _,
        by rw [hprog_me, StateTransitionSpec.clientResult_pure],
        by rw [hprog_me, StateTransitionSpec.clientState_pure]⟩
      S3.s3_fr (fun _ h => absurd rfl h)
      ⟨C.hpop_props.1.trans W.hib, C.hpop_props.2.1.trans W.hnb, C.hpop_props.2.2.1,
        C.hpop_props.2.2.2 ▸ W.hic_ge⟩
      S3.s3_sh hsc
      (by rw [C.hpop_props.2.2.2]
          exact le_trans (Nat.add_le_add_left S3.s3_rem_anti _) W.hcap_rem)
      hnd1 (fun _ hi => hi) (fun p hp => .inl ⟨p.2, hp, le_rfl⟩) hent_prop1
      (fun h0 => absurd rfl h0) fun W' hW'D hW'r hcost_eq =>
        ⟨?_, by dsimp only [djpRank]; simp [C.hcont]⟩
    have hc : (memoryCost (partDjpAddVert ⟨L.toEnv, cid, C.hpop_h, C.it₀.val, C.vOut.val,
        a.size, a.tLen⟩) C.s₁ : ℚ) ≤ 12 := by
      rw [hcost_eq, hprog_me, memoryCost_pure, add_zero]
      exact_mod_cast Nat.add_le_add_right S3.copy_cost 4
    have hrem_q : (remDeg n L.offBase C.s3.mem (Finset.univ.filter (fun x : Fin n =>
          dead0 x.val ≠ 0) ∪ C.D'.treeVerts C.D'.numSteps) : ℚ) ≤
        remDeg n L.offBase s.mem (deadSet ∪ W.D.treeVerts W.D.numSteps) := by
      exact_mod_cast S3.s3_rem_anti
    dsimp only [djpPot]; rw [C.hpop_props.2.2.2, hW'r, hW'D, hlen_w, hrem_d0]
    simp only [Nat.cast_add, Nat.cast_one, C.hcont, ↓reduceIte]; linarith
  by_cases hd0 : dead0 C.vOut.val ≠ 0
  · exact hstop_post 1 (.inl ⟨rfl, hd0⟩)
  · have hd0' : dead0 C.vOut.val = 0 := not_not.mp hd0
    by_cases hmax : L.maxsize ≤ a.size + 1
    · exact hstop_post 0 (.inr ⟨rfl, hd0', hmax⟩)
    · have hsz1_lt : a.size + 1 < L.maxsize := by omega
      have hdeg_pos : C.vOut ∉ deadSet ∪ W.D.treeVerts W.D.numSteps := by
        simp only [Finset.mem_union, deadSet, Finset.mem_filter, Finset.mem_univ, true_and, not_or]
        exact ⟨fun h => h hd0', C.hvOut_not⟩
      have hrem_ins : remDeg n L.offBase C.s3.mem (deadSet ∪ C.D'.treeVerts C.D'.numSteps) +
          (C.s3.mem (L.offBase + C.vOut.val + 1) - C.s3.mem (L.offBase + C.vOut.val)) =
          remDeg n L.offBase s.mem (deadSet ∪ W.D.treeVerts W.D.numSteps) := by
        rw [show deadSet ∪ C.D'.treeVerts C.D'.numSteps =
            insert C.vOut (deadSet ∪ W.D.treeVerts W.D.numSteps) by
              rw [htv_eq, Finset.union_insert],
          remDeg_insert hdeg_pos, S3.s3_rem_eq]
      have hcap_exp : C.hpop_h.itemCount +
          (C.s3.mem (L.offBase + C.vOut.val + 1) - C.s3.mem (L.offBase + C.vOut.val)) ≤ 2 * m := by
        have := W.hcap_rem
        change a.sh.itemCount + remDeg n L.offBase s.mem (deadSet ∪ W.D.treeVerts W.D.numSteps) ≤
          2 * m at this
        rw [C.hpop_props.2.2.2]; omega
      have hno_dup1 : ∀ p ∈ forestEntries C.roots₁, ∃ e' : Fin m, p.1.val = e'.val ∧
          ((L.es[e'.val]'e'.isLt).u = C.vOut ∨ (L.es[e'.val]'e'.isLt).v = C.vOut →
            ∃ nb : Fin n, (((L.es[e'.val]'e'.isLt).u = C.vOut ∧
                (L.es[e'.val]'e'.isLt).v = nb) ∨ ((L.es[e'.val]'e'.isLt).v = C.vOut ∧
                (L.es[e'.val]'e'.isLt).u = nb)) ∧ C.s3.mem (L.bufBase + n + nb.val) = cid) :=
        fun p hp => by
          rcases C.hent1 p hp with ⟨c₀, hc₀, _⟩
          rcases W.hent_prop (p.1, c₀) hc₀ with ⟨e', he'_id, _, _, _, he'_old⟩
          refine ⟨e', he'_id, fun hinc => ?_⟩
          rcases hinc with hu_v | hv_v
          · exact ⟨(L.es[e'.val]'e'.isLt).v, .inl ⟨hu_v, rfl⟩, (S3.s3_incur_in _
              (htv_eq ▸ Finset.mem_insert_of_mem
                (he'_old.elim (fun hu => absurd (hu_v ▸ hu) C.hvOut_not) id))).1⟩
          · exact ⟨(L.es[e'.val]'e'.isLt).u, .inr ⟨hv_v, rfl⟩, (S3.s3_incur_in _
              (htv_eq ▸ Finset.mem_insert_of_mem
                (he'_old.elim id (fun hv => absurd (hv_v ▸ hv) C.hvOut_not)))).1⟩
      have hexp := partExpandVertex_spec L cid ic0 nc0 C.vOut C.hpop_h C.roots₁ W.created C.s3
        edgeState0 S3.s3_fr (C.hpop_props.1.trans W.hib) (C.hpop_props.2.1.trans W.hnb)
        C.hpop_props.2.2.1 S3.s3_sh S3.hcsr3 S3.hin3 S3.s3_edgeState
        (fun p hp => S3.s3_sh.origKey_le_ckey p hp) C.hsimp hnd1 hno_dup1 hcap_exp
      set exp_h := (Memory.spec 0).clientResult C.s3
        (partExpandVertex ⟨L.toEnv, cid, C.vOut.val, C.hpop_h⟩)
      set exp_s := (Memory.spec 0).clientState C.s3
        (partExpandVertex ⟨L.toEnv, cid, C.vOut.val, C.hpop_h⟩)
      rcases hexp with ⟨hexp_safe, hexp_vh, hexp_fr, _, hexp_mod, hexp_ib, hexp_nb, hexp_rt,
        hexp_ic1, hexp_ic2, roots', created', hexp_sh, hexp_cost, hexp_len, hexp_nd, hexp_keep,
        hexp_ent, hexp_cov⟩
      have hprog_me : partDjpMaybeExpand
          ⟨L.toEnv, cid, C.hpop_h, C.vOut.val, 0, a.size + 1, a.tLen + 1⟩ =
          (partExpandVertex ⟨L.toEnv, cid, C.vOut.val, C.hpop_h⟩ >>= fun h' =>
            pure ⟨1, 0, a.size + 1, a.tLen + 1, h'⟩) := by
        rw [partDjpMaybeExpand_def, ite_eq_right (by omega : ¬((0 : ℕ) ≠ 0)),
          ite_eq_right (by dsimp only [PartLayout.toEnv]; exact not_le_of_gt hsz1_lt)]
      have hagree_exp := L.agree_outside_inSHPool (C.hpop_props.1.trans W.hib)
        (C.hpop_props.2.1.trans W.hnb) (fun x hx => by
          simpa only [InSHPool, C.hpop_props.1, C.hpop_props.2.1, W.hib, W.hnb]
            using hexp_mod x hx)
      have hrem_exp : remDeg n L.offBase exp_s.mem (deadSet ∪ C.D'.treeVerts C.D'.numSteps) =
          remDeg n L.offBase C.s3.mem (deadSet ∪ C.D'.treeVerts C.D'.numSteps) :=
        remDeg_congr _ fun k _ => hagree_exp.1 _ (by have := L.csr_lt_itemBase; omega)
      have hent_r' : ∀ p ∈ forestEntries roots',
          (∃ c₀, (p.1, c₀) ∈ forestEntries C.roots₁ ∧ c₀ ≤ p.2) ∨ ∃ e' : Fin m,
            p.1.val = e'.val ∧ (((L.es[e'.val]'e'.isLt).u = C.vOut ∧
              (L.es[e'.val]'e'.isLt).v ∉ W.D.treeVerts W.D.numSteps) ∨ ((L.es[e'.val]'e'.isLt).v =
              C.vOut ∧ (L.es[e'.val]'e'.isLt).u ∉ W.D.treeVerts W.D.numSteps)) := fun p hp => by
        rcases hexp_ent p hp with hc₀ | ⟨e', he'_id, _, _, _, ⟨hu, hv⟩ | ⟨hv, hu⟩⟩
        · exact .inl hc₀
        · exact .inr ⟨e', he'_id, .inl ⟨hu, fun hm => hv
            (S3.s3_incur_in _ (htv_eq ▸ Finset.mem_insert_of_mem hm)).1⟩⟩
        · exact .inr ⟨e', he'_id, .inr ⟨hv, fun hm => hu
            (S3.s3_incur_in _ (htv_eq ▸ Finset.mem_insert_of_mem hm)).1⟩⟩
      have hent_prop' : ∀ p ∈ forestEntries roots', ∃ e' : Fin m,
          p.1.val = e'.val ∧ p.1.origKey = (L.es[e'.val]'e'.isLt).weight ∧ p.1.origKey ≤ p.2 ∧
          edgeState0 e'.val = 0 ∧ ((L.es[e'.val]'e'.isLt).u ∈ C.D'.treeVerts C.D'.numSteps ∨
            (L.es[e'.val]'e'.isLt).v ∈ C.D'.treeVerts C.D'.numSteps) := fun p hp => by
        rcases hexp_ent p hp with ⟨c₁, hc₁, _⟩ | ⟨e', h1, h2, h3, h4, ⟨hu, _⟩ | ⟨hv, _⟩⟩
        · exact hent_prop1 (p.1, c₁) hc₁ |>.imp fun e' ⟨a1, a2, _, a4, a5⟩ =>
            ⟨a1, a2, hexp_sh.origKey_le_ckey p hp, a4, a5⟩
        · exact ⟨e', h1, h2, h3, h4, .inl (htv_eq ▸ hu ▸ Finset.mem_insert_self _ _)⟩
        · exact ⟨e', h1, h2, h3, h4, .inr (htv_eq ▸ hv ▸ Finset.mem_insert_self _ _)⟩
      have hcont_cov' : (1 : ℕ) ≠ 0 → ∀ e' : Fin m, edgeState0 e'.val = 0 →
          ((L.es[e'.val]'e'.isLt).u ∈ C.D'.treeVerts C.D'.numSteps ↔
            (L.es[e'.val]'e'.isLt).v ∉ C.D'.treeVerts C.D'.numSteps) →
          ∃ p ∈ forestEntries roots', p.1.val = e'.val := by
        intro _ e' he' hcross; rw [htv_eq] at hcross
        have hfrom_old : ((L.es[e'.val]'e'.isLt).u ∈ W.D.treeVerts W.D.numSteps ↔
              (L.es[e'.val]'e'.isLt).v ∉ W.D.treeVerts W.D.numSteps) →
            ∃ p ∈ forestEntries roots', p.1.val = e'.val := fun hcross_old => by
          rcases W.hcont_cov C.hcont e' he' hcross_old with ⟨p₀, hp₀, hp₀_id⟩
          refine forest_mem_of_pop_ne C.hperm1 hexp_keep C.he_id hp₀ hp₀_id fun heeq => ?_
          subst heeq; rcases C.hm_ends with ⟨hu, hv⟩ | ⟨hv, hu⟩
          · exact (hcross.mp (Finset.mem_insert_of_mem (hu ▸ C.hvIn_mem)))
              (hv ▸ Finset.mem_insert_self _ _)
          · exact (hcross.mp (hu ▸ Finset.mem_insert_self _ _))
              (Finset.mem_insert_of_mem (hv ▸ C.hvIn_mem))
        by_cases hu_old : (L.es[e'.val]'e'.isLt).u ∈ W.D.treeVerts W.D.numSteps
        · exact hfrom_old ⟨fun _ h => (hcross.mp (Finset.mem_insert_of_mem hu_old))
            (Finset.mem_insert_of_mem h), fun _ => hu_old⟩
        · by_cases hv_old : (L.es[e'.val]'e'.isLt).v ∈ W.D.treeVerts W.D.numSteps
          · exact hfrom_old ⟨fun h => absurd h hu_old, fun h => absurd hv_old h⟩
          · have hinc := edge_cross_insert_imp (inCur := fun x => C.s3.mem (L.bufBase + n + x))
              (fun x hx => S3.s3_incur_out x (htv_eq ▸ hx)) C.hincur₀_ne hu_old hv_old hcross
            rcases hexp_cov e' he' hinc with ⟨p, hp, hp1, _⟩; exact ⟨p, hp, hp1⟩
      have hcap_exp' : exp_h.itemCount + remDeg n L.offBase exp_s.mem (Finset.univ.filter
          (fun x : Fin n => dead0 x.val ≠ 0) ∪ C.D'.treeVerts C.D'.numSteps) ≤ 2 * m := by
        have h1 : exp_h.itemCount ≤ a.sh.itemCount +
            (C.s3.mem (L.offBase + C.vOut.val + 1) - C.s3.mem (L.offBase + C.vOut.val)) := by
          simpa only [C.hpop_props.2.2.2] using hexp_ic2
        have h2 : remDeg n L.offBase exp_s.mem (Finset.univ.filter
            (fun x : Fin n => dead0 x.val ≠ 0) ∪ C.D'.treeVerts C.D'.numSteps) +
            (C.s3.mem (L.offBase + C.vOut.val + 1) - C.s3.mem (L.offBase + C.vOut.val)) =
            remDeg n L.offBase s.mem (deadSet ∪ W.D.treeVerts W.D.numSteps) := by
          change remDeg n L.offBase exp_s.mem (deadSet ∪ C.D'.treeVerts C.D'.numSteps) + _ = _
          rw [hrem_exp]; exact hrem_ins
        have h3 : a.sh.itemCount + remDeg n L.offBase s.mem (deadSet ∪ W.D.treeVerts W.D.numSteps) ≤
            2 * m := W.hcap_rem
        omega
      have hs'_mod_s3 : ∀ x, exp_s.mem x ≠ C.s3.mem x →
          InSHPool ic0 nc0 (2 * m) (4 * m) C.hpop_h x := fun x hx => by
        simpa only [InSHPool, C.hpop_props.1, C.hpop_props.2.1, W.hib, W.hnb] using hexp_mod x hx
      refine partDjpPopped_addVert_finish C S3 1 0 exp_h roots' created' exp_s
        ⟨by rw [hd0', partDjpMaybeExpandSafe_def]; exact ⟨h16, fun _ _ => hexp_safe⟩,
          by rw [hd0', hprog_me]; exact validHistory_bind_step hexp_vh (validHistory_pure w _ _),
          by rw [hd0', hprog_me, StateTransitionSpec.clientResult_bind,
            StateTransitionSpec.clientResult_pure],
          by rw [hd0', hprog_me, StateTransitionSpec.clientState_bind,
            StateTransitionSpec.clientState_pure]⟩
        (hexp_fr.trans S3.s3_fr) hs'_mod_s3 ⟨hexp_ib.trans (C.hpop_props.1.trans W.hib),
          hexp_nb.trans (C.hpop_props.2.1.trans W.hnb), hexp_rt,
          W.hic_ge.trans (C.hpop_props.2.2.2 ▸ hexp_ic1)⟩
        hexp_sh (.inr (.inr ⟨rfl, rfl, hd0', hsz1_lt⟩)) hcap_exp' hexp_nd hexp_keep hent_r'
        hent_prop' hcont_cov' fun W' hW'D hW'r hcost_eq => ?_
      have hic_max : exp_h.itemCount ≤ 2 * L.es.length := hexp_sh.ic_max
      have hsub1 : a.sh.itemCount ≤ exp_h.itemCount := C.hpop_props.2.2.2 ▸ hexp_ic1
      have hlen_exp : (forestItems roots').length =
          (forestItems C.roots₁).length + (exp_h.itemCount - a.sh.itemCount) := by
        rw [C.hpop_props.2.2.2] at hexp_len; exact hexp_len
      refine ⟨?_, ?_⟩
      · have hc : (memoryCost (partDjpAddVert ⟨L.toEnv, cid, C.hpop_h, C.it₀.val, C.vOut.val,
              a.size, a.tLen⟩) C.s₁ : ℚ) + totalPhi partRankThreshold roots' ≤
            totalPhi partRankThreshold C.roots₁ + 14 +
              2450 * (C.s3.mem (L.offBase + C.vOut.val + 1)
              - C.s3.mem (L.offBase + C.vOut.val) : ℚ) := by
          rw [hcost_eq, hd0', hprog_me, memoryCost_bind', memoryCost_pure, add_zero,
            Nat.cast_add, Nat.cast_add]
          have hcopy_q : (memoryCost (partCopyIndexedEdge ⟨L.edgeBase, L.bufBase + 10 * n,
              C.it₀.val, a.tLen⟩) C.s₁ : ℚ) ≤ 8 := by exact_mod_cast S3.copy_cost
          rw [Nat.cast_sub (S3.hcsr3.off_mono C.vOut)] at hexp_cost
          push_cast at hexp_cost ⊢; linarith
        have hrem_q : (remDeg n L.offBase exp_s.mem (deadSet ∪ C.D'.treeVerts C.D'.numSteps) : ℚ) +
            (C.s3.mem (L.offBase + C.vOut.val + 1) - C.s3.mem (L.offBase + C.vOut.val) : ℚ) =
            remDeg n L.offBase s.mem (deadSet ∪ W.D.treeVerts W.D.numSteps) := by
          have hq := congrArg (Nat.cast (R := ℚ)) hrem_ins
          rw [Nat.cast_add, Nat.cast_sub (S3.hcsr3.off_mono C.vOut), ← hrem_exp] at hq; exact hq
        have hic_q : ((2 * L.es.length - exp_h.itemCount : ℕ) : ℚ) +
            ((forestItems roots').length : ℚ) = ((2 * L.es.length - a.sh.itemCount : ℕ) : ℚ) +
            ((forestItems C.roots₁).length : ℚ) := by
          rw [Nat.cast_sub hic_max, Nat.cast_sub W.hic_le, hlen_exp, Nat.cast_add,
            Nat.cast_sub hsub1]; linarith
        have hlen_w_q : ((forestItems W.roots).length : ℚ) = (forestItems C.roots₁).length + 1 :=
          by exact_mod_cast hlen_w
        have hrem_d : remDeg n L.offBase exp_s.mem (Finset.univ.filter (fun x : Fin n =>
              dead0 x.val ≠ 0) ∪ C.D'.treeVerts C.D'.numSteps) =
            remDeg n L.offBase exp_s.mem (deadSet ∪ C.D'.treeVerts C.D'.numSteps) := rfl
        dsimp only [djpPot]; rw [hW'r, hW'D, hrem_d, hrem_d0]
        simp only [Nat.one_ne_zero, ↓reduceIte, C.hcont]
        have har := djpPot_addVert_arith (P₀ := totalPhi partRankThreshold W.roots)
          hc hrem_q hic_q hlen_w_q
        linarith
      · dsimp only [djpRank]; rw [hW'r]
        simp only [Nat.one_ne_zero, ↓reduceIte, C.hcont]
        have hsub2 : a.sh.itemCount ≤ 2 * L.es.length := W.hic_le
        have := exp_h.itemCount; omega

private theorem partDjpPopped_spec
    (W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s)
    (hcsr₀ : HoldsUndirCSR L.offBase L.adjBase L.es s₀.mem)
    (hin₀ : HoldsIndexedEdges L.edgeBase L.es s₀.mem)
    (hdead₀ : ∀ x < n, s₀.mem (L.bufBase + x) = dead0 x)
    (hedge₀ : ∀ i < L.es.length, s₀.mem (L.bufBase + 14 * n + i) = edgeState0 i)
    (hincur₀_ne : ∀ x < n, inCur0 x ≠ cid) (hcid_fit : Fits w cid)
    (hsimp : ∀ e : Fin L.es.length, (L.es[e.val]'e.isLt).u ≠ (L.es[e.val]'e.isLt).v)
    (hcont : a.cont ≠ 0) (hpop_h : SHHandle) (it₀ : SHItem) (popKey : ℕ) (roots₁ : List SHTree)
    (s₁ : Memory.State) (hpop_props : hpop_h.itemBase = a.sh.itemBase ∧
      hpop_h.nodeBase = a.sh.nodeBase ∧ hpop_h.rankThreshold = partRankThreshold ∧
      hpop_h.itemCount = a.sh.itemCount) (hs1_fr : s₁.frontier = s.frontier)
    (hs1_mod : ∀ x, s₁.mem x ≠ s.mem x →
      InSHPool ic0 nc0 (2 * L.es.length) (4 * L.es.length) a.sh x)
    (hit0_mem : (it₀, popKey) ∈ forestEntries W.roots)
    (hit0_min : ∀ p ∈ forestEntries W.roots, popKey ≤ p.2)
    (hsh1 : SHInv w ic0 nc0 (2 * L.es.length) (4 * L.es.length) hpop_h roots₁ W.created s₁)
    (hperm1 : (it₀ :: forestItems roots₁).Perm (forestItems W.roots))
    (hent1 : ∀ p ∈ forestEntries roots₁, ∃ c₀, (p.1, c₀) ∈ forestEntries W.roots ∧ c₀ ≤ p.2) :
    let d : PartDjpDispatchArgs := ⟨L.toEnv, cid, hpop_h, it₀.val, a.hitPrev, a.size, a.tLen⟩
    DjpStepPost W (partDjpDispatch d) partDjpDispatchSafe d s₁ 251 roots₁ := by
  let m := L.es.length
  let d : PartDjpDispatchArgs := ⟨L.toEnv, cid, hpop_h, it₀.val, a.hitPrev, a.size, a.tLen⟩
  have h16 := L.h16
  have hhit0 : a.hitPrev = 0 := by by_contra hne; exact hcont (W.hhit_prev hne).2.1
  have hagree_s1 := L.agree_outside_inSHPool W.hib W.hnb hs1_mod
  have hin1 := (L.congr_below_itemBase hagree_s1.1).1 (djpWitness_edges W hin₀)
  rcases W.hent_prop (it₀, popKey) hit0_mem with ⟨eIdx, he_id, he_ok, he_le, he_st0, he_inc⟩
  have hu_lt := (L.es[eIdx.val]'eIdx.isLt).u.isLt; have hv_lt := (L.es[eIdx.val]'eIdx.isLt).v.isLt
  have he_lt_fr : L.edgeBase + 4 * it₀.val + 1 < s₁.frontier := by
    have := L.edge_lt_itemBase; have := L.hit_nd; have := L.hnd_buf
    rw [hs1_fr, W.hfr, he_id]; omega
  have hu_eq : s₁.mem (L.edgeBase + 4 * it₀.val) = (L.es[eIdx.val]'eIdx.isLt).u.val := by
    rw [he_id]; exact (hin1 eIdx.val eIdx.isLt).1
  have hv_eq : s₁.mem (L.edgeBase + 4 * it₀.val + 1) = (L.es[eIdx.val]'eIdx.isLt).v.val := by
    rw [he_id]; exact (hin1 eIdx.val eIdx.isLt).2.1
  have hu_fr : L.bufBase + n + s₁.mem (L.edgeBase + 4 * it₀.val) < s₁.frontier := by
    rw [hu_eq, hs1_fr, W.hfr]; omega
  have hv_fr : L.bufBase + n + s₁.mem (L.edgeBase + 4 * it₀.val + 1) < s₁.frontier := by
    rw [hv_eq, hs1_fr, W.hfr]; omega
  have hs1_buf : ∀ x, L.bufBase ≤ x → x < L.bufBase + 4 * n → s₁.mem x = s.mem x :=
    fun x hx1 _ => hagree_s1.2 x hx1
  let cu := s₁.mem (L.bufBase + n + (L.es[eIdx.val]'eIdx.isLt).u.val)
  let cv := s₁.mem (L.bufBase + n + (L.es[eIdx.val]'eIdx.isLt).v.val)
  have hdisp_eval : ∀ tail, (tail = if cu = cid ∧ cv = cid then
        pure ⟨1, a.hitPrev, a.size, a.tLen, hpop_h⟩
      else partDjpAddVert ⟨L.toEnv, cid, hpop_h, it₀.val,
        if cu = cid then (L.es[eIdx.val]'eIdx.isLt).v.val else (L.es[eIdx.val]'eIdx.isLt).u.val,
        a.size, a.tLen⟩) →
      ((Memory.spec w).ValidHistory s₁ ((Memory.spec w).clientHistory s₁ tail) →
        (Memory.spec w).ValidHistory s₁ ((Memory.spec w).clientHistory s₁ (partDjpDispatch d))) ∧
      (Memory.spec 0).clientResult s₁ (partDjpDispatch d) = (Memory.spec 0).clientResult s₁ tail ∧
      (Memory.spec 0).clientState s₁ (partDjpDispatch d) = (Memory.spec 0).clientState s₁ tail ∧
      memoryCost (partDjpDispatch d) s₁ = 4 + memoryCost tail s₁ := by
    rintro tail rfl; rw [partDjpDispatch_def]; dsimp only [d, PartLayout.toEnv]
    refine ⟨fun ht => validHistory_read_bind (by omega) (validHistory_read_bind he_lt_fr
        (validHistory_read_bind hu_fr (validHistory_read_bind hv_fr
          (by rw [hu_eq, hv_eq]; exact ht)))), ?_, ?_, ?_⟩
    · rw [clientResult_bind_read, clientResult_bind_read, clientResult_bind_read,
        clientResult_bind_read, hu_eq, hv_eq]
    · rw [clientState_bind_read, clientState_bind_read, clientState_bind_read,
        clientState_bind_read, hu_eq, hv_eq]
    · rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
        memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
        memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
        memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, hu_eq, hv_eq]
      dsimp only [cu, cv]; omega
  by_cases hboth : cu = cid ∧ cv = cid
  · obtain ⟨W', hpot', hrank'⟩ := partDjpPopped_internal W hincur₀_ne hcont hpop_h it₀ roots₁ s₁
      hpop_props hs1_fr hs1_mod hsh1 hperm1 hent1 eIdx he_id hboth.1 hboth.2
    obtain ⟨hev_vh, hev_res, hev_s, hev_cost⟩ := hdisp_eval _ (ite_eq_left hboth).symm
    refine ⟨(by rw [partDjpDispatchSafe_def]; dsimp only [d, PartLayout.toEnv]; exact ⟨h16,
          he_lt_fr, hu_fr, hv_fr, fun hneg => by
            rw [hu_eq, hv_eq] at hneg; exact absurd hboth hneg⟩),
      hev_vh (validHistory_pure w _ _),
      by rw [hev_s, StateTransitionSpec.clientState_pure, hs1_fr, W.hfr],
      fun _ _ => by rw [hev_s, StateTransitionSpec.clientState_pure], ?_⟩
    rw [hev_res, hev_s, StateTransitionSpec.clientResult_pure,
      StateTransitionSpec.clientState_pure]
    refine ⟨W', ?_, hrank'⟩; rw [hev_cost, memoryCost_pure, add_zero]; push_cast; exact hpot'
  · have hstep_vout : ∀ (vIn vOut : Fin n) (hvIn_mem : vIn ∈ W.D.treeVerts W.D.numSteps)
        (hvOut_not : vOut ∉ W.D.treeVerts W.D.numSteps)
        (hm_ends : ((L.es[eIdx.val]'eIdx.isLt).u = vIn ∧ (L.es[eIdx.val]'eIdx.isLt).v = vOut) ∨
          ((L.es[eIdx.val]'eIdx.isLt).v = vIn ∧ (L.es[eIdx.val]'eIdx.isLt).u = vOut))
        (hv_if : (if cu = cid then (L.es[eIdx.val]'eIdx.isLt).v.val
          else (L.es[eIdx.val]'eIdx.isLt).u.val) = vOut.val),
        DjpStepPost W (partDjpDispatch d) partDjpDispatchSafe d s₁ 251 roots₁ := by
      intro vIn vOut hvIn_mem hvOut_not hm_ends hv_if
      rcases partDjpPopped_addVert_spec ⟨hcsr₀, hin₀, hdead₀, hedge₀, hincur₀_ne, hcid_fit, hsimp,
          hcont, hhit0, hpop_h, it₀, popKey, roots₁, s₁, hpop_props, hs1_fr, hs1_mod, hit0_mem,
          hit0_min, hsh1, hperm1, hent1, eIdx, he_id, he_st0, vIn, vOut, hvIn_mem, hvOut_not,
          hm_ends, he_ok ▸ he_le, fun s_step hcross => W.hwpop_fut s_step (it₀, popKey) hit0_mem
            ⟨he_id ▸ eIdx.isLt, by
              have heq_e : L.es[it₀.val]'(he_id ▸ eIdx.isLt) = L.es[eIdx.val]'eIdx.isLt :=
                congrArg (fun q : Fin L.es.length => L.es[q.val]'q.isLt)
                  (Fin.ext he_id : (⟨it₀.val, he_id ▸ eIdx.isLt⟩ : Fin L.es.length) = eIdx)
              rw [heq_e]; exact hcross⟩⟩ with
        ⟨hadd_safe, hadd_vh, hadd_fr, hadd_mod, W', hpot', hrank'⟩
      obtain ⟨hev_vh, hev_res, hev_s, hev_cost⟩ := hdisp_eval _ (by rw [ite_eq_right hboth, hv_if])
      refine ⟨(by
          rw [partDjpDispatchSafe_def]; dsimp only [d, PartLayout.toEnv]
          refine ⟨h16, he_lt_fr, hu_fr, hv_fr, fun _ => ?_⟩; simp only [hu_eq, hv_eq]
          change partDjpAddVertSafe w ⟨L.toEnv, cid, hpop_h, it₀.val,
            if cu = cid then (L.es[eIdx.val]'eIdx.isLt).v.val
            else (L.es[eIdx.val]'eIdx.isLt).u.val, a.size, a.tLen⟩ s₁
          rw [hv_if]; exact hadd_safe),
        hev_vh hadd_vh, by rw [hev_s]; exact hadd_fr,
        fun x hx => by rw [hev_s]; exact hadd_mod x hx, ?_⟩
      rw [hev_res, hev_s]; refine ⟨W', ?_, hrank'⟩
      rw [hev_cost, Nat.cast_add]; push_cast; linarith
    by_cases hcu : cu = cid
    · have hcv_ne : cv ≠ cid := fun h => hboth ⟨hcu, h⟩
      exact hstep_vout (L.es[eIdx.val]'eIdx.isLt).u (L.es[eIdx.val]'eIdx.isLt).v
        (djpWitness_mem_of_inCur_cid W hincur₀_ne _
          ((hs1_buf _ (by omega) (by omega)).symm.trans hcu))
        (fun hin => hcv_ne ((hs1_buf _ (by omega) (by omega)).trans (W.hincur_in _ hin).1))
        (.inl ⟨rfl, rfl⟩) (by simp [hcu])
    · have hu_not : (L.es[eIdx.val]'eIdx.isLt).u ∉ W.D.treeVerts W.D.numSteps := fun hin =>
        hcu ((hs1_buf _ (by omega) (by omega)).trans (W.hincur_in _ hin).1)
      exact hstep_vout (L.es[eIdx.val]'eIdx.isLt).v (L.es[eIdx.val]'eIdx.isLt).u
        (he_inc.elim (fun hu => absurd hu hu_not) id) hu_not (.inr ⟨rfl, rfl⟩) (by simp [hcu])

end WitnessVars

/-! ## Public Step, Round-Initialization, and DJP-Loop Specifications -/

/-- Specification of `partDjpStep`: executes one dynamic Soft-Heap DJP step, decreasing `djpRank`
and satisfying `(memoryCost prog s : ℚ) + djpPot W' ≤ djpPot W`. -/
theorem partDjpStep_spec {w n : ℕ} (L : PartLayout w n) (s₀ : Memory.State)
    (dead0 inCur0 edgeState0 : ℕ → ℕ) (cid ic0 nc0 tLen0 : ℕ) (u : Fin n)
    (hcsr₀ : HoldsUndirCSR L.offBase L.adjBase L.es s₀.mem)
    (hin₀ : HoldsIndexedEdges L.edgeBase L.es s₀.mem)
    (hdead₀ : ∀ x < n, s₀.mem (L.bufBase + x) = dead0 x)
    (hedge₀ : ∀ i < L.es.length, s₀.mem (L.bufBase + 14 * n + i) = edgeState0 i)
    (hincur₀_ne : ∀ x < n, inCur0 x ≠ cid) (hcid_fit : Fits w cid)
    (hsimp : ∀ e : Fin L.es.length, (L.es[e.val]'e.isLt).u ≠ (L.es[e.val]'e.isLt).v)
    (a : PartDjpState) (s : Memory.State)
    (W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a s)
    (hcont : a.cont ≠ 0) :
    let env := L.toEnv; let prog := partDjpStep (⟨env, cid⟩, a)
    let a' := (Memory.spec 0).clientResult s prog; let s' := (Memory.spec 0).clientState s prog
    partDjpStepSafe w (⟨env, cid⟩, a) s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧ (∀ x, ¬(InSHPool ic0 nc0 (2 * L.es.length) (4 * L.es.length)
      ⟨L.itemBase, L.nodeBase, 0, ic0, nc0, partRankThreshold⟩ x ∨
      (L.bufBase + n ≤ x ∧ x < L.bufBase + 4 * n) ∨
      (L.bufBase + 10 * n ≤ x ∧ x < L.bufBase + 14 * n)) → s'.mem x = s.mem x) ∧
    ∃ W' : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a' s',
      (memoryCost prog s : ℚ) + djpPot W' ≤ djpPot W ∧ djpRank W' < djpRank W := by
  let m := L.es.length; let env := L.toEnv; have h16 := L.h16
  have hfuel_fit : Fits w (500 * (2 * m + 1)) := by
    simpa [partSHFuel, shFuelBound, partRankThreshold] using L.hfit_fuel
  have hfuel_ge : shFuelBound a.sh.rankThreshold (2 * m) ≤ 500 * (2 * m + 1) := by
    rw [W.hrt]; dsimp only [shFuelBound, partRankThreshold]; exact le_rfl
  have hbuf_lt : L.bufBase < s.frontier := by have := L.hn_pos; rw [W.hfr]; omega
  rcases shExtractMin_spec W.hsh hfuel_ge hfuel_fit with
    ⟨hv_ext, hsafe_ext, h_ib, h_nb, h_ic, _, h_rt, hs1_fr, hs1_mod, hempty, hnonempty⟩
  set ext := (Memory.spec 0).clientResult s (shExtractMin (a.sh, 500 * (2 * m + 1)))
  set s₁ := (Memory.spec 0).clientState s (shExtractMin (a.sh, 500 * (2 * m + 1)))
  have hst_eval : ∀ tail, (tail = if ext.found = 0 then pure ⟨0, 0, a.size, a.tLen, ext.handle⟩
      else partDjpDispatch ⟨env, cid, ext.handle, ext.val, a.hitPrev, a.size, a.tLen⟩) →
      ((Memory.spec w).ValidHistory s₁ ((Memory.spec w).clientHistory s₁ tail) →
        (Memory.spec w).ValidHistory s
          ((Memory.spec w).clientHistory s (partDjpStep (⟨env, cid⟩, a)))) ∧
      (Memory.spec 0).clientResult s (partDjpStep (⟨env, cid⟩, a)) =
        (Memory.spec 0).clientResult s₁ tail ∧
      (Memory.spec 0).clientState s (partDjpStep (⟨env, cid⟩, a)) =
        (Memory.spec 0).clientState s₁ tail ∧
      memoryCost (partDjpStep (⟨env, cid⟩, a)) s = 1 +
        memoryCost (shExtractMin (a.sh, 500 * (2 * m + 1))) s + memoryCost tail s₁ := by
    rintro tail rfl; rw [partDjpStep_def]; dsimp only [env, PartLayout.toEnv]
    refine ⟨fun h2 => validHistory_read_bind hbuf_lt (validHistory_bind_step hv_ext h2),
      ?_, ?_, ?_⟩
    · rw [clientResult_bind_read, StateTransitionSpec.clientResult_bind]
    · rw [clientState_bind_read, StateTransitionSpec.clientState_bind]
    · rw [memoryCost_bind', memoryCost_read, clientState_read, memoryCost_bind']
      dsimp only [m, ext, s₁]; omega
  by_cases hf0 : ext.found = 0
  · have hroots_nil : W.roots = [] := by by_contra hne; have := (hnonempty hne).1; omega
    rcases hempty hroots_nil with ⟨_, _, _, hext_h, hs1_eq, hcost_ext⟩
    have hhit0 : a.hitPrev = 0 := by by_contra hne; exact hcont (W.hhit_prev hne).2.1
    obtain ⟨hev_vh, hev_res, hev_s, hev_cost⟩ := hst_eval _ (ite_eq_left hf0).symm
    let W' : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u
        ⟨0, 0, a.size, a.tLen, a.sh⟩ s :=
      { roots := W.roots, created := W.created, D := W.D, treeIndexed := W.treeIndexed,
        hfr := W.hfr, hmod := W.hmod, hib := W.hib, hnb := W.hnb, hrt := W.hrt,
        hic_ge := W.hic_ge, hic_le := W.hic_le, hsh := W.hsh, hroot := W.hroot,
        hsize := W.hsize, hsize_le := W.hsize_le, htlen := W.htlen, htlen_le := W.htlen_le,
        htlen_dead := W.htlen_dead, htree_len := W.htree_len, htree_w := W.htree_w,
        htree_src := W.htree_src, htree_mem := W.htree_mem, hverts_mem := W.hverts_mem,
        hincur_in := W.hincur_in, hincur_out := W.hincur_out,
        hstop_dead := fun x hx hdx => absurd (W.hno_hit hhit0 x hx) hdx,
        hhit_prev := fun hne => absurd rfl hne, hno_hit := fun _ => W.hno_hit hhit0,
        hcap_rem := W.hcap_rem, hnd_edge := W.hnd_edge, hent_prop := W.hent_prop,
        hcont_cov := fun h0 => absurd rfl h0, hcut_cov := W.hcut_cov, hwpop_fut := W.hwpop_fut,
        hempty_stop := fun _ _ _ eIdx he_st hcross => (by
          rcases W.hcont_cov hcont eIdx he_st hcross with ⟨p, hp, _⟩
          rw [hroots_nil] at hp; cases hp),
        hcont_size := fun h0 => absurd rfl h0 }
    have hsafe_step : partDjpStepSafe w (⟨env, cid⟩, a) s := by
      rw [partDjpStepSafe_def]; dsimp only [env, PartLayout.toEnv]
      exact ⟨h16, hfuel_fit, hbuf_lt, hsafe_ext, fun hne => absurd hf0 hne⟩
    refine ⟨hsafe_step,
      hev_vh (by rw [hs1_eq]; exact validHistory_pure w _ _),
      by rw [hev_s, StateTransitionSpec.clientState_pure, hs1_eq],
      fun _ _ => by rw [hev_s, StateTransitionSpec.clientState_pure, hs1_eq], ?_⟩
    rw [hev_res, hev_s, StateTransitionSpec.clientResult_pure,
      StateTransitionSpec.clientState_pure,
      hext_h, hs1_eq]
    refine ⟨W', ?_, by dsimp only [djpRank]; simp [hcont]⟩
    rw [hev_cost, hcost_ext, hs1_eq, memoryCost_pure]; dsimp only [djpPot]
    simp only [hcont, ↓reduceIte]; push_cast; linarith
  · have hroots_ne : W.roots ≠ [] := fun hnil => hf0 (hempty hnil).1
    rcases hnonempty hroots_ne with ⟨_, it₀, roots₁, hit0_mem, hit0_val, _, hit0_min, hsh1,
      hperm1, hent1, hphi_ext⟩
    rcases partDjpPopped_spec W hcsr₀ hin₀ hdead₀ hedge₀ hincur₀_ne hcid_fit hsimp hcont ext.handle
        it₀ ext.key roots₁ s₁ ⟨h_ib, h_nb, h_rt.trans W.hrt, h_ic⟩ hs1_fr hs1_mod hit0_mem
        hit0_min hsh1 hperm1 hent1 with
      ⟨hdisp_safe, hdisp_vh, hdisp_fr, hdisp_mod, W', hpot', hrank'⟩
    obtain ⟨hev_vh, hev_res, hev_s, hev_cost⟩ := hst_eval _ (by rw [ite_eq_right hf0, ← hit0_val])
    refine ⟨(by rw [partDjpStepSafe_def]; dsimp only [env, PartLayout.toEnv]; exact ⟨h16,
          hfuel_fit, hbuf_lt, hsafe_ext, fun _ => by rw [← hit0_val]; exact hdisp_safe⟩),
      hev_vh hdisp_vh, by rw [hev_s, hdisp_fr], fun x hx => by
        rw [hev_s, hdisp_mod x hx]; by_contra hne
        exact hx (.inl (by simpa only [InSHPool, W.hib, W.hnb] using hs1_mod x hne)), ?_⟩
    rw [hev_res, hev_s]; refine ⟨W', ?_, hrank'⟩
    rw [W.hrt] at hphi_ext; rw [hev_cost, Nat.cast_add, Nat.cast_add, Nat.cast_one]; linarith

private theorem partRoundInit_mkWitness {w n : ℕ} (L : PartLayout w n) (s₀ : Memory.State)
    (dead0 inCur0 edgeState0 : ℕ → ℕ) (cid ic0 nc0 tLen0 : ℕ) (u : Fin n)
    (hu_alive : dead0 u.val = 0)
    (htLen_dead : tLen0 ≤ (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)).card)
    (cont0 : ℕ) (h' : SHHandle) (roots' : List SHTree) (created' : ℕ → ℕ) (s' : Memory.State)
    (hs'_fr : s'.frontier = L.bufBase + (14 * n + 14 * L.es.length))
    (hs'_mod : ∀ x, s'.mem x ≠ s₀.mem x → InSHPool ic0 nc0 (2 * L.es.length) (4 * L.es.length)
      ⟨L.itemBase, L.nodeBase, 0, ic0, nc0, partRankThreshold⟩ x ∨
      (L.bufBase + n ≤ x ∧ x < L.bufBase + 4 * n))
    (hh' : h'.itemBase = L.itemBase ∧ h'.nodeBase = L.nodeBase ∧
      h'.rankThreshold = partRankThreshold ∧ ic0 ≤ h'.itemCount)
    (hsh' : SHInv w ic0 nc0 (2 * L.es.length) (4 * L.es.length) h' roots' created' s')
    (hverts' : ∀ k, k < 1 → s'.mem (L.bufBase + 3 * n + k) = u.val)
    (hincur_in' : ∀ x : Fin n, x ∈ ({u} : Finset (Fin n)) → s'.mem (L.bufBase + n + x.val) = cid ∧
      ∃ k < 1, s'.mem (L.bufBase + 3 * n + k) = x.val ∧ s'.mem (L.bufBase + 2 * n + x.val) = k)
    (hincur_out' : ∀ x : Fin n, x ∉ ({u} : Finset (Fin n)) →
      s'.mem (L.bufBase + n + x.val) = inCur0 x.val)
    (hcap_rem' : h'.itemCount + remDeg n L.offBase s'.mem
      (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0) ∪ {u}) ≤ 2 * L.es.length)
    (hnd' : ((forestItems roots').map SHItem.val).Nodup)
    (hent_prop' : ∀ p ∈ forestEntries roots', ∃ e' : Fin L.es.length, p.1.val = e'.val ∧
      p.1.origKey = (L.es[e'.val]'e'.isLt).weight ∧ p.1.origKey ≤ p.2 ∧ edgeState0 e'.val = 0 ∧
      ((L.es[e'.val]'e'.isLt).u ∈ ({u} : Finset (Fin n)) ∨
       (L.es[e'.val]'e'.isLt).v ∈ ({u} : Finset (Fin n))))
    (hcont_cov' : cont0 ≠ 0 → ∀ e' : Fin L.es.length, edgeState0 e'.val = 0 →
      ((L.es[e'.val]'e'.isLt).u ∈ ({u} : Finset (Fin n)) ↔
        (L.es[e'.val]'e'.isLt).v ∉ ({u} : Finset (Fin n))) →
      ∃ p ∈ forestEntries roots', p.1.val = e'.val)
    (hempty_stop' : cont0 = 0 → 0 = 0 → 1 < L.maxsize → ∀ e' : Fin L.es.length,
      edgeState0 e'.val = 0 → ¬((L.es[e'.val]'e'.isLt).u ∈ ({u} : Finset (Fin n)) ↔
        (L.es[e'.val]'e'.isLt).v ∉ ({u} : Finset (Fin n))))
    (hcont_size' : cont0 ≠ 0 → 1 < L.maxsize) :
    ∃ W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u
        ⟨cont0, 0, 1, tLen0, h'⟩ s',
      W.roots = roots' ∧ W.D.treeVerts W.D.numSteps = {u} := by
  let D₀ : DynamicDJPTree n := ⟨0, u, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0,
    fun s => Fin.elim0 s, fun s => Fin.elim0 s, fun s => Fin.elim0 s, fun s => Fin.elim0 s,
    fun s => Fin.elim0 s⟩
  have hD0_verts : D₀.treeVerts D₀.numSteps = {u} := by
    simp [D₀, DynamicDJPTree.treeVerts, djpVerts]
  have htlen_le : tLen0 ≤ n := by
    have hcard := (Finset.card_le_univ (Finset.univ.filter fun x : Fin n =>
      dead0 x.val ≠ 0)).trans_eq (Fintype.card_fin n)
    omega
  refine ⟨{
    roots := roots', created := created', D := D₀, treeIndexed := [], hfr := hs'_fr,
    hmod := fun x hx => (hs'_mod x hx).imp id fun h => .inl h,
    hib := hh'.1, hnb := hh'.2.1, hrt := hh'.2.2.1, hic_ge := hh'.2.2.2,
    hic_le := hsh'.ic_max, hsh := hsh', hroot := rfl, hsize := rfl, hsize_le := L.hmax_pos,
    htlen := rfl, htlen_le := htlen_le, htlen_dead := by simpa [D₀] using htLen_dead,
    htree_len := rfl, htree_w := rfl, htree_src := fun _ h => (by cases h),
    htree_mem := fun _ hi => (by simp at hi),
    hverts_mem := fun k hk => by
      have hk0 := Nat.lt_one_iff.mp hk; subst hk0
      simp only [djpVertsList, D₀, List.getElem_cons_zero]; exact hverts' 0 hk,
    hincur_in := hD0_verts ▸ hincur_in', hincur_out := hD0_verts ▸ hincur_out',
    hstop_dead := fun x hx hdx => by
      rw [hD0_verts, Finset.mem_singleton] at hx; subst hx; exact absurd hu_alive hdx,
    hhit_prev := fun h => absurd rfl h,
    hno_hit := fun _ x hx => by
      rw [hD0_verts, Finset.mem_singleton] at hx; subst hx; exact hu_alive,
    hcap_rem := hD0_verts ▸ hcap_rem', hnd_edge := hnd',
    hent_prop := hD0_verts ▸ hent_prop', hcont_cov := hD0_verts ▸ hcont_cov',
    hcut_cov := fun _ _ _ ⟨s, _⟩ => Fin.elim0 s, hwpop_fut := fun s => Fin.elim0 s,
    hempty_stop := hD0_verts ▸ hempty_stop', hcont_size := hcont_size' }, rfl, hD0_verts⟩

/-- Specification of `partRoundInit`: initializes `D₀ = {u}`, expands `u` when `1 < maxsize`,
and builds the initial `DjpWitness` within amortized cost `+15` over `2450 * remDeg`. -/
theorem partRoundInit_spec {w n : ℕ} (L : PartLayout w n)
    (dead0 inCur0 edgeState0 : ℕ → ℕ) (cid ic0 nc0 tLen0 : ℕ) (u : Fin n)
    (h₀ : SHHandle) (s₀ : Memory.State)
    (hfr₀ : s₀.frontier = L.bufBase + (14 * n + 14 * L.es.length))
    (hib₀ : h₀.itemBase = L.itemBase) (hnb₀ : h₀.nodeBase = L.nodeBase)
    (hrt₀ : h₀.rankThreshold = partRankThreshold) (hic₀_eq : h₀.itemCount = ic0)
    (hsh₀ : SHInv w ic0 nc0 (2 * L.es.length) (4 * L.es.length) h₀ [] (fun _ => 0) s₀)
    (hcsr₀ : HoldsUndirCSR L.offBase L.adjBase L.es s₀.mem)
    (hin₀ : HoldsIndexedEdges L.edgeBase L.es s₀.mem)
    (hincur₀ : ∀ x < n, s₀.mem (L.bufBase + n + x) = inCur0 x)
    (hincur₀_ne : ∀ x < n, inCur0 x ≠ cid) (hcid_fit : Fits w cid) (hu_alive : dead0 u.val = 0)
    (hedge₀ : ∀ i < L.es.length, s₀.mem (L.bufBase + 14 * n + i) = edgeState0 i)
    (hsimp : ∀ e : Fin L.es.length, (L.es[e.val]'e.isLt).u ≠ (L.es[e.val]'e.isLt).v)
    (htLen_dead : tLen0 ≤ (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)).card)
    (hcap_rem₀ : ic0 + remDeg n L.offBase s₀.mem
      (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)) ≤ 2 * L.es.length) :
    let d : PartExpandVertexArgs := ⟨L.toEnv, cid, u.val, h₀⟩
    let prog := partRoundInit d; let h' := (Memory.spec 0).clientResult s₀ prog
    let s' := (Memory.spec 0).clientState s₀ prog; let cont0 := if L.maxsize ≤ 1 then 0 else 1
    partRoundInitSafe w d s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    s'.frontier = s₀.frontier ∧ (∀ x, ¬(InSHPool ic0 nc0 (2 * L.es.length) (4 * L.es.length)
      ⟨L.itemBase, L.nodeBase, 0, ic0, nc0, partRankThreshold⟩ x ∨
      (L.bufBase + n ≤ x ∧ x < L.bufBase + 4 * n)) → s'.mem x = s₀.mem x) ∧
    ∃ W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u
        ⟨cont0, 0, 1, tLen0, h'⟩ s',
      (memoryCost prog s₀ : ℚ) + djpPot W ≤
        2450 * (remDeg n L.offBase s₀.mem
          (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)) : ℚ) +
        275 * (2 * L.es.length - ic0 : ℕ) + 15 := by
  let m := L.es.length; let d : PartExpandVertexArgs := ⟨L.toEnv, cid, u.val, h₀⟩
  let deadSet : Finset (Fin n) := Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)
  let s₁ : Memory.State := ⟨write3Mem L.bufBase n 0 cid u.val s₀.mem, s₀.frontier⟩
  have h16 := L.h16; have hn_pos := L.hn_pos; have hwf₀ := hsh₀.wf
  have hu_fit : Fits w u.val := L.hfit_end.of_le (by omega)
  have h0_fit : Fits w 0 := h16.of_le (by omega)
  have hs1_below : ∀ x < L.itemBase, s₁.mem x = s₀.mem x := fun x hx => by
    have := L.hit_nd; have := L.hnd_buf
    exact write3Mem_agree_outside (by omega) (by omega) (by omega)
  have hin₁ := (L.congr_below_itemBase hs1_below).1 hin₀
  have hcsr₁ := (L.congr_below_itemBase hs1_below).2 hcsr₀
  have hs1_sh : SHInv w ic0 nc0 (2 * m) (4 * m) h₀ [] (fun _ => 0) s₁ :=
    hsh₀.congr_outside (write3Mem_wf hwf₀ hu_fit hcid_fit h0_fit) rfl fun a' ha' => by
      rcases L.inSHPool_lt_bufBase hib₀ hnb₀ ha' with ⟨h1, h2⟩
      exact write3Mem_agree_outside (by omega) (by omega) (by omega)
  have hs1_hedge : ∀ i < m, s₁.mem (L.bufBase + 14 * n + i) = edgeState0 i := fun i hi =>
    (write3Mem_agree_outside (by omega) (by omega) (by omega)).trans (hedge₀ i hi)
  have hs1_mod : ∀ x, s₁.mem x ≠ s₀.mem x → L.bufBase + n ≤ x ∧ x < L.bufBase + 4 * n :=
    fun _ hx => write3Mem_in_range u.isLt hn_pos hx
  have hu_not_dead : u ∉ deadSet := by simp [deadSet, hu_alive]
  have hrem_ins : remDeg n L.offBase s₁.mem (deadSet ∪ {u}) +
      (s₁.mem (L.offBase + u.val + 1) - s₁.mem (L.offBase + u.val)) =
      remDeg n L.offBase s₀.mem deadSet := by
    have hreq : remDeg n L.offBase s₁.mem deadSet = remDeg n L.offBase s₀.mem deadSet :=
      remDeg_congr _ fun k _ => hs1_below (L.offBase + k) (by have := L.csr_lt_itemBase; omega)
    rw [← hreq, show deadSet ∪ {u} = insert u deadSet by rw [Finset.union_comm, Finset.insert_eq]]
    exact remDeg_insert hu_not_dead
  have hs1_verts : ∀ k, k < 1 → s₁.mem (L.bufBase + 3 * n + k) = u.val := fun k hk => by
    have hk0 := Nat.lt_one_iff.mp hk; subst hk0; dsimp only [s₁, write3Mem]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  have ⟨hs1_in_ins, hs1_out_ins⟩ := write3Mem_incur (cid := cid) (inCur0 := inCur0)
    (mem := s₀.mem) (S := ∅) (Finset.notMem_empty u) hn_pos (fun _ h => by simp at h)
    fun x _ => hincur₀ x.val x.isLt
  have hs1_in : ∀ x : Fin n, x ∈ ({u} : Finset (Fin n)) → s₁.mem (L.bufBase + n + x.val) = cid ∧
      ∃ k < 1, s₁.mem (L.bufBase + 3 * n + k) = x.val ∧ s₁.mem (L.bufBase + 2 * n + x.val) = k :=
    fun x hx => hs1_in_ins x (by simpa using hx)
  have hs1_out : ∀ x : Fin n, x ∉ ({u} : Finset (Fin n)) →
      s₁.mem (L.bufBase + n + x.val) = inCur0 x.val :=
    fun x hx => hs1_out_ins x (by simpa using hx)
  have hs1_def : ⟨Function.update (Function.update (Function.update s₀.mem
      (L.bufBase + 3 * n) u.val) (L.bufBase + n + u.val) cid)
      (L.bufBase + 2 * n + u.val) 0, s₀.frontier⟩ = s₁ := by
    dsimp only [s₁, write3Mem]; simp only [Nat.add_zero]
  have hr_eval : ∀ tail, (L.maxsize ≤ 1 → tail = pure h₀) →
      (¬ L.maxsize ≤ 1 → tail = partExpandVertex d) →
      ((Memory.spec w).ValidHistory s₁ ((Memory.spec w).clientHistory s₁ tail) →
        (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (partRoundInit d))) ∧
      (Memory.spec 0).clientResult s₀ (partRoundInit d) = (Memory.spec 0).clientResult s₁ tail ∧
      (Memory.spec 0).clientState s₀ (partRoundInit d) = (Memory.spec 0).clientState s₁ tail ∧
      memoryCost (partRoundInit d) s₀ = 3 + memoryCost tail s₁ := by
    intro tail ht1 ht2; rw [partRoundInit_def]
    have htail_eq : (if d.env.maxsize ≤ 1 then pure d.sh else partExpandVertex d) = tail := by
      by_cases hm : d.env.maxsize ≤ 1
      · rw [ite_eq_left hm]; exact (ht1 hm).symm
      · rw [ite_eq_right hm]; exact (ht2 hm).symm
    rw [htail_eq]; dsimp only [d, PartLayout.toEnv]
    refine ⟨fun htail => validHistory_write_bind (by rw [hfr₀]; omega) hu_fit
        (validHistory_write_bind (by dsimp only; rw [hfr₀]; omega) hcid_fit
          (validHistory_write_bind (by dsimp only; rw [hfr₀]; omega) h0_fit
            (by rw [hs1_def]; exact htail))), ?_, ?_, ?_⟩
    · rw [clientResult_bind_write, clientResult_bind_write, clientResult_bind_write, hs1_def]
    · rw [clientState_bind_write, clientState_bind_write, clientState_bind_write, hs1_def]
    · rw [memoryCost_bind', memoryCost_write, clientState_write, memoryCost_bind',
        memoryCost_write, clientState_write, memoryCost_bind', memoryCost_write, clientState_write]
      dsimp only; rw [hs1_def]; omega
  by_cases hmax1 : L.maxsize ≤ 1
  · obtain ⟨hev_vh, hev_res, hev_s, hev_cost⟩ :=
      hr_eval _ (fun _ => rfl) (fun h => absurd hmax1 h)
    obtain ⟨W, hW_r, hW_tv⟩ := partRoundInit_mkWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0
      tLen0 u hu_alive htLen_dead 0 h₀ [] (fun _ => 0) s₁ hfr₀
      (fun _ hx => .inr (hs1_mod _ hx)) ⟨hib₀, hnb₀, hrt₀, hic₀_eq ▸ le_rfl⟩ hs1_sh hs1_verts
      hs1_in hs1_out (by
        rw [hic₀_eq]; have := hcap_rem₀
        change ic0 + remDeg n L.offBase s₀.mem deadSet ≤ 2 * m at this
        change ic0 + remDeg n L.offBase s₁.mem (deadSet ∪ {u}) ≤ 2 * m; omega)
      (by dsimp only [forestItems, forestEntries]; simp)
      (fun _ hp => by simp [forestEntries] at hp)
      (fun h => absurd rfl h) (fun _ _ hlt => absurd hlt (not_lt_of_ge hmax1))
      (fun h => absurd rfl h)
    refine ⟨(by rw [partRoundInitSafe_def]; dsimp only [d, PartLayout.toEnv]; exact ⟨h16,
          by rw [hfr₀]; omega, by rw [hfr₀]; omega, by rw [hfr₀]; omega, fun h => absurd hmax1 h⟩),
      hev_vh (validHistory_pure w _ _), by rw [hev_s, StateTransitionSpec.clientState_pure],
      fun x hx => by
        rw [hev_s, StateTransitionSpec.clientState_pure]
        by_contra hne; exact hx (.inr (hs1_mod x hne)), ?_⟩
    rw [ite_eq_left hmax1, hev_res, hev_s, StateTransitionSpec.clientResult_pure,
      StateTransitionSpec.clientState_pure]; refine ⟨W, ?_⟩
    have hrem_q : (remDeg n L.offBase s₁.mem (Finset.univ.filter (fun x : Fin n =>
          dead0 x.val ≠ 0) ∪ {u}) : ℚ) ≤
        remDeg n L.offBase s₀.mem (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)) := by
      exact_mod_cast (show remDeg n L.offBase s₁.mem (deadSet ∪ {u}) ≤
        remDeg n L.offBase s₀.mem deadSet by omega)
    dsimp only [djpPot]
    rw [hW_tv, hW_r, hic₀_eq, totalPhi_nil, hev_cost, memoryCost_pure, add_zero,
      show ((forestItems ([] : List SHTree)).length : ℚ) = 0 by simp [forestItems, forestEntries]]
    simp only [↓reduceIte, Nat.cast_ofNat]; linarith
  · have hmax_gt : 1 < L.maxsize := by omega
    have hcap_exp : h₀.itemCount +
        (s₁.mem (L.offBase + u.val + 1) - s₁.mem (L.offBase + u.val)) ≤ 2 * m := by
      rw [hic₀_eq]; have := hcap_rem₀
      change ic0 + remDeg n L.offBase s₀.mem deadSet ≤ 2 * m at this; omega
    have hexp := partExpandVertex_spec L cid ic0 nc0 u h₀ [] (fun _ => 0) s₁ edgeState0 hfr₀
      hib₀ hnb₀ hrt₀ hs1_sh hcsr₁ hin₁ hs1_hedge (fun _ h => by simp [forestEntries] at h)
      hsimp (by dsimp only [forestItems, forestEntries]; simp)
      (fun _ h => by simp [forestEntries] at h) hcap_exp
    set h' := (Memory.spec 0).clientResult s₁ (partExpandVertex d)
    set s' := (Memory.spec 0).clientState s₁ (partExpandVertex d)
    rcases hexp with ⟨hexp_safe, hexp_vh, hexp_fr, _, hexp_mod, hexp_ib, hexp_nb, hexp_rt,
      hexp_ic1, hexp_ic2, roots', created', hexp_sh, hexp_cost, hexp_len, hexp_nd, _, hexp_ent,
      hexp_cov⟩
    obtain ⟨hev_vh, hev_res, hev_s, hev_cost⟩ :=
      hr_eval _ (fun h => absurd h hmax1) (fun _ => rfl)
    have hagree_exp := L.agree_outside_inSHPool hib₀ hnb₀ hexp_mod
    have hmod_all : ∀ x, s'.mem x ≠ s₀.mem x → InSHPool ic0 nc0 (2 * m) (4 * m)
        ⟨L.itemBase, L.nodeBase, 0, ic0, nc0, partRankThreshold⟩ x ∨
        (L.bufBase + n ≤ x ∧ x < L.bufBase + 4 * n) := fun x hx => by
      by_cases hdiff : s'.mem x = s₁.mem x
      · exact .inr (hs1_mod x (hdiff ▸ hx))
      · exact .inl (by simpa only [InSHPool, hib₀, hnb₀] using hexp_mod x hdiff)
    have hrem_exp : remDeg n L.offBase s'.mem (deadSet ∪ {u}) =
        remDeg n L.offBase s₁.mem (deadSet ∪ {u}) :=
      remDeg_congr _ fun k _ => hagree_exp.1 _ (by have := L.csr_lt_itemBase; omega)
    have hin_in' : ∀ x : Fin n, x ∈ ({u} : Finset (Fin n)) →
        s'.mem (L.bufBase + n + x.val) = cid ∧ ∃ k < 1,
          s'.mem (L.bufBase + 3 * n + k) = x.val ∧ s'.mem (L.bufBase + 2 * n + x.val) = k :=
      fun x hx => by
        obtain ⟨h1, k, hk, h2, h3⟩ := hs1_in x hx
        exact ⟨(hagree_exp.2 _ (by omega)).trans h1, k, hk,
          (hagree_exp.2 _ (by omega)).trans h2, (hagree_exp.2 _ (by omega)).trans h3⟩
    have hin_out' : ∀ x : Fin n, x ∉ ({u} : Finset (Fin n)) →
        s'.mem (L.bufBase + n + x.val) = inCur0 x.val := fun x hx =>
      (hagree_exp.2 _ (by omega)).trans (hs1_out x hx)
    obtain ⟨W, hW_r, hW_tv⟩ := partRoundInit_mkWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0
      tLen0 u hu_alive htLen_dead 1 h' roots' created' s' (hexp_fr.trans hfr₀)
      hmod_all ⟨hexp_ib.trans hib₀, hexp_nb.trans hnb₀, hexp_rt, hic₀_eq ▸ hexp_ic1⟩ hexp_sh
      (fun k hk => (hagree_exp.2 _ (by omega)).trans (hs1_verts k hk)) hin_in' hin_out'
      (by change h'.itemCount + remDeg n L.offBase s'.mem (deadSet ∪ {u}) ≤ 2 * m; rw [hrem_exp]
          have h1 : h'.itemCount ≤ ic0 +
              (s₁.mem (L.offBase + u.val + 1) - s₁.mem (L.offBase + u.val)) := hic₀_eq ▸ hexp_ic2
          have h2 : ic0 + remDeg n L.offBase s₀.mem deadSet ≤ 2 * m := hcap_rem₀; omega)
      hexp_nd
      (fun p hp => by
        rcases hexp_ent p hp with ⟨c₀, hc₀, _⟩ | ⟨e', h1, h2, h3, h4, ⟨hu, _⟩ | ⟨hv, _⟩⟩
        · simp [forestEntries] at hc₀
        · exact ⟨e', h1, h2, h3, h4, .inl (hu ▸ Finset.mem_singleton_self _)⟩
        · exact ⟨e', h1, h2, h3, h4, .inr (hv ▸ Finset.mem_singleton_self _)⟩)
      (fun _ e' he' hcross => by
        have hinc := edge_cross_insert_imp (inCur := fun x => s₁.mem (L.bufBase + n + x))
          (fun x hx => hs1_out x (by simpa using hx)) hincur₀_ne (Finset.notMem_empty _)
          (Finset.notMem_empty _) (by simpa using hcross)
        rcases hexp_cov e' he' hinc with ⟨p, hp, hp1, _⟩; exact ⟨p, hp, hp1⟩)
      (fun h0 => absurd h0 Nat.one_ne_zero) (fun _ => hmax_gt)
    refine ⟨(by rw [partRoundInitSafe_def]; dsimp only [d, PartLayout.toEnv]; exact ⟨h16,
          by rw [hfr₀]; omega, by rw [hfr₀]; omega, by rw [hfr₀]; omega, fun _ => hexp_safe⟩),
      hev_vh hexp_vh, by rw [hev_s, hexp_fr], fun x hx => by
        rw [hev_s]; by_contra hne; exact hx (hmod_all x hne), ?_⟩
    rw [ite_eq_right hmax1, hev_res, hev_s]; refine ⟨W, ?_⟩
    have hlen' : (forestItems roots').length = h'.itemCount - ic0 := by
      rw [hic₀_eq, show (forestItems []).length = 0 by simp [forestItems, forestEntries],
        Nat.zero_add] at hexp_len; exact hexp_len
    have hic_max : h'.itemCount ≤ 2 * L.es.length := hexp_sh.ic_max
    have hic_q : ((2 * L.es.length - h'.itemCount : ℕ) : ℚ) + ((forestItems roots').length : ℚ) =
        ((2 * L.es.length - ic0 : ℕ) : ℚ) := by
      rw [Nat.cast_sub hic_max, Nat.cast_sub (hic₀_eq ▸ hsh₀.ic_max), hlen',
        Nat.cast_sub (hic₀_eq ▸ hexp_ic1)]; linarith
    have hrem_q : (remDeg n L.offBase s'.mem (deadSet ∪ {u}) : ℚ) +
        (s₁.mem (L.offBase + u.val + 1) - s₁.mem (L.offBase + u.val) : ℚ) =
        remDeg n L.offBase s₀.mem deadSet := by
      have hq := congrArg (Nat.cast (R := ℚ)) hrem_ins
      rw [Nat.cast_add, Nat.cast_sub (hcsr₁.off_mono u), ← hrem_exp] at hq; exact hq
    have hrem_d : remDeg n L.offBase s'.mem (Finset.univ.filter (fun x : Fin n =>
          dead0 x.val ≠ 0) ∪ {u}) = remDeg n L.offBase s'.mem (deadSet ∪ {u}) := rfl
    have hrem_d0 : remDeg n L.offBase s₀.mem (Finset.univ.filter (fun x : Fin n =>
          dead0 x.val ≠ 0)) = remDeg n L.offBase s₀.mem deadSet := rfl
    dsimp only [djpPot]
    rw [hW_r, hW_tv, hrem_d, hrem_d0, hic_q, hev_cost, Nat.cast_add,
      Nat.cast_sub (hcsr₁.off_mono u)] at *
    simp only [totalPhi_nil] at hexp_cost; push_cast; linarith

/-- Full specification of `partDjpLoop`: terminates with `cont = 0`, produces a final
`DjpWitness`, frames `[inCur, compVerts)` / Soft-Heap slice / round DJP tree slice, and obeys
`(memoryCost prog s₁ : ℚ) + djpPot W' ≤ djpPot W₀`. -/
theorem partDjpLoop_spec {w n : ℕ} (L : PartLayout w n) (s₀ : Memory.State)
    (dead0 inCur0 edgeState0 : ℕ → ℕ) (cid ic0 nc0 tLen0 : ℕ) (u : Fin n)
    (hcsr₀ : HoldsUndirCSR L.offBase L.adjBase L.es s₀.mem)
    (hin₀ : HoldsIndexedEdges L.edgeBase L.es s₀.mem)
    (hdead₀ : ∀ x < n, s₀.mem (L.bufBase + x) = dead0 x)
    (hedge₀ : ∀ i < L.es.length, s₀.mem (L.bufBase + 14 * n + i) = edgeState0 i)
    (hincur₀_ne : ∀ x < n, inCur0 x ≠ cid) (hcid_fit : Fits w cid)
    (hsimp : ∀ e : Fin L.es.length, (L.es[e.val]'e.isLt).u ≠ (L.es[e.val]'e.isLt).v)
    (h₀ : SHHandle) (s₁ : Memory.State)
    (W₀ : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u
      ⟨if L.maxsize ≤ 1 then 0 else 1, 0, 1, tLen0, h₀⟩ s₁) :
    let d : PartDjpLoopArgs := ⟨L.toEnv, cid, tLen0, h₀⟩; let prog := partDjpLoop d
    let a' := (Memory.spec 0).clientResult s₁ prog; let s' := (Memory.spec 0).clientState s₁ prog
    partDjpLoopSafe w d s₁ ∧
    (Memory.spec w).ValidHistory s₁ ((Memory.spec w).clientHistory s₁ prog) ∧
    a'.cont = 0 ∧ s'.frontier = s₁.frontier ∧ (∀ x, ¬(InSHPool ic0 nc0 (2 * L.es.length)
      (4 * L.es.length) ⟨L.itemBase, L.nodeBase, 0, ic0, nc0, partRankThreshold⟩ x ∨
      (L.bufBase + n ≤ x ∧ x < L.bufBase + 4 * n) ∨
      (L.bufBase + 10 * n ≤ x ∧ x < L.bufBase + 14 * n)) → s'.mem x = s₁.mem x) ∧
    ∃ W' : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u a' s',
      (memoryCost prog s₁ : ℚ) + djpPot W' ≤ djpPot W₀ := by
  let m := L.es.length; let d : PartDjpLoopArgs := ⟨L.toEnv, cid, tLen0, h₀⟩
  generalize hc0 : (if L.maxsize ≤ 1 then 0 else 1) = c0 at W₀
  by_cases hmax1 : L.maxsize ≤ 1
  · have hc0_eq : c0 = 0 := hc0.symm.trans (by simp [hmax1]); subst hc0_eq
    have hprog : partDjpLoop d = pure ⟨0, 0, 1, tLen0, h₀⟩ := by
      rw [partDjpLoop_def]; dsimp only [d, PartLayout.toEnv]; simp only [hmax1, ↓reduceIte]
    refine ⟨by rw [partDjpLoopSafe_def]; exact ⟨L.h16, fun hneg => absurd hmax1 hneg⟩,
      by rw [hprog]; exact validHistory_pure w _ _,
      by rw [hprog, StateTransitionSpec.clientResult_pure],
      by rw [hprog, StateTransitionSpec.clientState_pure],
      fun _ _ => by rw [hprog, StateTransitionSpec.clientState_pure], ?_⟩
    rw [hprog, memoryCost_pure, StateTransitionSpec.clientResult_pure,
      StateTransitionSpec.clientState_pure]; exact ⟨W₀, by simp⟩
  · have hc0_eq : c0 = 1 := hc0.symm.trans (by simp [hmax1]); subst hc0_eq
    let S : Set ℕ := {x |
      InSHPool ic0 nc0 (2 * m) (4 * m) ⟨L.itemBase, L.nodeBase, 0, ic0, nc0, partRankThreshold⟩ x ∨
      (L.bufBase + n ≤ x ∧ x < L.bufBase + 4 * n) ∨
      (L.bufBase + 10 * n ≤ x ∧ x < L.bufBase + 14 * n)}
    let WType := Σ p : PartDjpState × Memory.State,
      DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u p.1 p.2
    let I (wt : WType) (a : PartDjpState) (s : Memory.State) : Prop := wt.1.1 = a ∧ wt.1.2 = s
    have hzero : ∀ wt a s, I wt a s → djpRank wt.2 = 0 → ¬(a.cont ≠ 0) := by
      rintro ⟨⟨a', s'⟩, W⟩ a s ⟨rfl, rfl⟩ hr hne; dsimp only [djpRank] at hr; simp [hne] at hr
    have hstep : ∀ wt a s, I wt a s → a.cont ≠ 0 →
        partDjpStepSafe w (⟨L.toEnv, cid⟩, a) s ∧ (Memory.spec w).ValidHistory s
          ((Memory.spec w).clientHistory s (partDjpStep (⟨L.toEnv, cid⟩, a))) ∧
        let a' := (Memory.spec 0).clientResult s (partDjpStep (⟨L.toEnv, cid⟩, a))
        let s' := (Memory.spec 0).clientState s (partDjpStep (⟨L.toEnv, cid⟩, a))
        ∃ wt' : WType, I wt' a' s' ∧
          (memoryCost (partDjpStep (⟨L.toEnv, cid⟩, a)) s : ℚ) + djpPot wt'.2 ≤ djpPot wt.2 + 0 ∧
          Memory.Modifies S s s' ∧ djpRank wt'.2 < djpRank wt.2 := by
      rintro ⟨⟨a', s'⟩, W⟩ a s ⟨rfl, rfl⟩ hne
      obtain ⟨hsafe_s, hv_s, hfr_s, hmod_s, W', hpot_s, hrank_s⟩ :=
        partDjpStep_spec L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u
          hcsr₀ hin₀ hdead₀ hedge₀ hincur₀_ne hcid_fit hsimp a' s' W hne
      exact ⟨hsafe_s, hv_s, ⟨⟨_, _⟩, W'⟩, ⟨rfl, rfl⟩, le_trans hpot_s (le_of_eq (add_zero _).symm),
        ⟨le_of_eq hfr_s.symm, fun x _ hx => hmod_s x hx⟩, hrank_s⟩
    have hrank0 : djpRank (⟨⟨⟨1, 0, 1, tLen0, h₀⟩, s₁⟩, W₀⟩ : WType).2 ≤ 2 * m + 1 := by
      dsimp only [djpRank]; simp only [Nat.one_ne_zero, ↓reduceIte]
      have hlen := shInv_forestItems_length_le W₀.hsh
      have h1 := W₀.hic_ge; have h2 := W₀.hic_le; dsimp only at hlen h1 h2; omega
    have hbw := boundedWhile_rat_witness_spec (fun _ (s : PartDjpState) => s.cont ≠ 0)
      partDjpStep partDjpStepSafe w ⟨L.toEnv, cid⟩ (0 : ℚ) (le_refl 0)
      I (fun wt => djpRank wt.2) (fun wt => djpPot wt.2) S hzero hstep
      (2 * m + 1) ⟨⟨⟨1, 0, 1, tLen0, h₀⟩, s₁⟩, W₀⟩ ⟨1, 0, 1, tLen0, h₀⟩ s₁ ⟨rfl, rfl⟩ hrank0
    have hprog : partDjpLoop d =
        boundedWhile (fun _ (s : PartDjpState) => s.cont ≠ 0)
          partDjpStep ⟨L.toEnv, cid⟩ (2 * m + 1) ⟨1, 0, 1, tLen0, h₀⟩ := by
      rw [partDjpLoop_def]; dsimp only [d, PartLayout.toEnv, m]; simp only [hmax1, ↓reduceIte]
    rw [← hprog] at hbw
    rcases hbw with ⟨hsafe_bw, hv_bw, hstop_bw, hmod_bw, ⟨⟨a', s'⟩, W'⟩, ⟨rfl, rfl⟩, hpot_bw⟩
    have hfr_eq : ((Memory.spec 0).clientState s₁ (partDjpLoop d)).frontier = s₁.frontier :=
      W'.hfr.trans W₀.hfr.symm
    refine ⟨by rw [partDjpLoopSafe_def]; exact ⟨L.h16, fun _ => hsafe_bw⟩, hv_bw,
      not_not.mp hstop_bw, hfr_eq, fun x hxS => ?_, W', ?_⟩
    · by_cases hx : x < s₁.frontier
      · exact hmod_bw.2 x hx hxS
      · have ha : ((Memory.spec w).clientState s₁ (partDjpLoop d)).frontier ≤ x := by
          rw [clientState_width w, hfr_eq]; omega
        simpa only [clientState_width w] using
          Memory.mem_clientState_of_frontier_le s₁ (partDjpLoop d) hv_bw ha
    · simpa only [zero_mul, add_zero] using hpot_bw

end Cslib.Algorithms.WordRAM.MinimumSpanningForest
