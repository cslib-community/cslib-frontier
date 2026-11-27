/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Kruskal
public import CslibFrontier.Computability.WordRAM.Realization.RecordOps
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.UpdateSimp
import CslibFrontier.Tactic.ValidProg

/-!
# Indexed Edge Layouts, Initialization, and Emission on the Word RAM

Defines `IndexedEdge` (`IndexedEdge.toWeighted`), the stride-4 memory layout predicate
`HoldsIndexedEdges` (paired with `Kruskal.HoldsEdges` for stride-3 raw edge arrays), shared
argument bundles (`GraphSlice`, `SelectedEdgesArgs`), and linear-time edge initialization and
materialization routines (`initIndexedEdges`, `emitMSFEdges`, `emitIndexedEdgesFromIdxs`) built on
`Memory.FramedTriple`, `Memory.allocBlockDirty`, `LoopFrame`, and `word_enc_structure`.

## Main definitions

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.IndexedEdge`, `IndexedEdge.toWeighted`:
  weighted edge on `Fin n` tagged with its original input edge identifier `id`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.HoldsIndexedEdges`: word-RAM memory layout
  predicate for stride-4 indexed edge arrays.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.GraphSlice`, `SelectedEdgesArgs`: faithful
  three-word argument structures encoded via `word_enc_structure`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.initIndexedEdges`: initializes a stride-4
  `IndexedEdge` array from raw stride-3 `Kruskal.encode` input in `O(m)` time.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.emitMSFEdges`: materializes a length-prefixed
  `Kruskal.encodeEdges` output array from selected original edge indices in `O(k)` time.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.emitIndexedEdgesFromIdxs`: materializes a
  stride-4 `IndexedEdge` array from selected edge indices in `O(k)` time.

## Main results

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_initIndexedEdges`,
  `initIndexedEdges_spec`
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_emitMSFEdges`,
  `emitMSFEdges_spec`
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_emitIndexedEdgesFromIdxs`,
  `emitIndexedEdgesFromIdxs_spec`
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Algorithms.WordRAM.Kruskal

/-! ## Edge Records, Layouts, and Shared Argument Structures -/

/-- Weighted graph edge on `Fin n` tagged with its original input edge identifier `id`. -/
structure IndexedEdge (n : ℕ) where
  /-- First endpoint vertex. -/
  u : Fin n
  /-- Second endpoint vertex. -/
  v : Fin n
  /-- Edge weight. -/
  weight : ℕ
  /-- Original input edge identifier preserved across contractions. -/
  id : ℕ
  deriving DecidableEq

/-- Forget the edge identifier to obtain a `WeightedEdge n ℕ`. -/
@[expose] def IndexedEdge.toWeighted {n : ℕ} (e : IndexedEdge n) : WeightedEdge n ℕ :=
  ⟨e.u, e.v, e.weight⟩

/-- Memory `mem` stores `es` in stride-4 `(u, v, weight, id)` layout starting at `base`. -/
abbrev HoldsIndexedEdges {n : ℕ} (base : ℕ) (es : List (IndexedEdge n)) (mem : ℕ → ℕ) : Prop :=
  ∀ i (hi : i < es.length),
    mem (base + 4 * i) = es[i].u.val ∧
    mem (base + 4 * i + 1) = es[i].v.val ∧
    mem (base + 4 * i + 2) = es[i].weight ∧
    mem (base + 4 * i + 3) = es[i].id

/-- Framing lemma for `HoldsIndexedEdges`. -/
theorem HoldsIndexedEdges.congr {n : ℕ} {base : ℕ} {es : List (IndexedEdge n)}
    {m₁ m₂ : ℕ → ℕ}
    (heq : ∀ a, base ≤ a → a < base + 4 * es.length → m₂ a = m₁ a)
    (h : HoldsIndexedEdges base es m₁) : HoldsIndexedEdges base es m₂ := fun i hi => by
  rcases h i hi with ⟨hu, hv, hw, hid⟩
  exact ⟨(heq _ (by omega) (by omega)).trans hu, (heq _ (by omega) (by omega)).trans hv,
    (heq _ (by omega) (by omega)).trans hw, (heq _ (by omega) (by omega)).trans hid⟩

/-- Reconstructs a length-`m` list of `IndexedEdge n` values satisfying `HoldsIndexedEdges` from
pointwise endpoint bounds `< n` in raw memory `mem`. -/
theorem exists_indexedEdges_of_mem_lt {n base m : ℕ} {mem : ℕ → ℕ}
    (h : ∀ j < m, mem (base + 4 * j) < n ∧ mem (base + 4 * j + 1) < n) :
    ∃ es : List (IndexedEdge n), es.length = m ∧ HoldsIndexedEdges base es mem := by
  refine ⟨List.ofFn fun k : Fin m =>
    ⟨⟨mem (base + 4 * k.val), (h k.val k.isLt).1⟩,
     ⟨mem (base + 4 * k.val + 1), (h k.val k.isLt).2⟩,
     mem (base + 4 * k.val + 2), mem (base + 4 * k.val + 3)⟩, by simp, fun i hi => by
    simp only [List.getElem_ofFn]; trivial⟩

/-- Preserves `HoldsIndexedEdges base es` across any `Memory.FramedTriple` whose modified set `S`
is disjoint from `[base, base + 4 * es.length)` below `s.frontier`. -/
theorem holdsIndexedEdges_frame_mem {α : Type} {w c n base : ℕ} {S : Set ℕ}
    {s : Memory.State} {p : Memory.Prog α} {es : List (IndexedEdge n)}
    {Q : α → Memory.State → Prop}
    (h : Memory.FramedTriple w s p c S Q) (hes : HoldsIndexedEdges base es s.mem)
    (hdisj : Disjoint S (Set.Ico base (base + 4 * es.length)))
    (halloc : base + 4 * es.length ≤ s.frontier) :
    Memory.FramedTriple w s p c S fun a s' => Q a s' ∧ HoldsIndexedEdges base es s'.mem :=
  h.frame_mem hes (fun _ _ hEq hm => HoldsIndexedEdges.congr (fun a ha1 ha2 =>
    (hEq a (Set.mem_Ico.mpr ⟨ha1, ha2⟩)).symm) hm)
    hdisj (fun _ ha => by simp only [Set.mem_Ico] at ha; omega)

/-- Reference to a stride-4 `IndexedEdge` array of `numEdges` edges on `Fin numVertices`
vertices stored at `edgeBase`. -/
structure GraphSlice where
  /-- Number of vertices `n`. -/
  numVertices : ℕ
  /-- Number of edges `m`. -/
  numEdges : ℕ
  /-- Base address of the stride-4 `IndexedEdge` array. -/
  edgeBase : ℕ

/-- Faithful three-word encoding of `GraphSlice` as `[numVertices, numEdges, edgeBase]`. -/
word_enc_structure encGraphSlice : GraphSlice where
  numVertices : wordWords,
  numEdges : wordWords,
  edgeBase : wordWords

instance : WordEncoding GraphSlice := ⟨3, encGraphSlice⟩

/-- Arguments for index-based edge emission: `count` edge indices at `selBase` referencing an
edge array at `srcBase`. -/
structure SelectedEdgesArgs where
  /-- Base address of the source edge array (stride-3 raw or stride-4 indexed). -/
  srcBase : ℕ
  /-- Base address of the `count` selected edge indices. -/
  selBase : ℕ
  /-- Number of selected edges to emit. -/
  count : ℕ

/-- Faithful three-word encoding of `SelectedEdgesArgs` as `[srcBase, selBase, count]`. -/
word_enc_structure encSelectedEdgesArgs : SelectedEdgesArgs where
  srcBase : wordWords,
  selBase : wordWords,
  count : wordWords

instance : WordEncoding SelectedEdgesArgs := ⟨3, encSelectedEdgesArgs⟩

/-! ## `initIndexedEdges`: Raw Stride-3 Input to Indexed Stride-4 Array -/

private structure InitEdgeEnv where
  inBase : ℕ
  outBase : ℕ

private word_enc_structure encInitEdgeEnv : InitEdgeEnv where
  inBase : wordWords,
  outBase : wordWords

private instance : WordEncoding InitEdgeEnv := ⟨2, encInitEdgeEnv⟩

private def initIndexedEdgesStep (x : InitEdgeEnv × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst x
  let idx := Prod.snd x
  let u ← Memory.read (env.inBase + 3 * idx)
  let v ← Memory.read (env.inBase + 3 * idx + 1)
  let wt ← Memory.read (env.inBase + 3 * idx + 2)
  Memory.write (env.outBase + 4 * idx) u
  Memory.write (env.outBase + 4 * idx + 1) v
  Memory.write (env.outBase + 4 * idx + 2) wt
  Memory.write (env.outBase + 4 * idx + 3) idx
  pure (idx + 1)

private def initIndexedEdgesStepSafe (w : ℕ) (x : InitEdgeEnv × ℕ) (_ : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w ((Prod.snd x) + 1)

private theorem realizes_initIndexedEdgesStep_history : Realizes .exact
    initIndexedEdgesStep (appendWords encInitEdgeEnv wordWords) wordWords
    (fun w d s => initIndexedEdgesStepSafe w d s ∧
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (initIndexedEdgesStep d)))
    (fun _ _ => 0) := by
  unfold initIndexedEdgesStep
  realize
  all_goals
    obtain ⟨⟨h16, hfit⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
      Memory.write, Memory.step_read, Memory.step_write, Memory.valid]
  all_goals fits

private theorem realizes_initIndexedEdgesStep : Realizes .exact
    initIndexedEdgesStep (appendWords encInitEdgeEnv wordWords) wordWords
    initIndexedEdgesStepSafe (fun _ _ => 0) :=
  realizes_initIndexedEdgesStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Copy `count` raw stride-3 edges starting at `inBase` into a newly allocated stride-4
`IndexedEdge` array (`(u, v, weight, idx)`), returning its base address. -/
def initIndexedEdges (inBase count : ℕ) : Memory.Prog ℕ := do
  let out ← Memory.allocBlockDirty (4 * count)
  let _ ← iterate initIndexedEdgesStep ⟨inBase, out.base⟩ count 0
  pure out.base

private theorem initIndexedEdges_word_spec {w inBase count : ℕ} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin_lt : inBase + 3 * count ≤ s.frontier)
    (hfit : Fits w (s.frontier + 4 * count)) :
    iterationSafe initIndexedEdgesStep initIndexedEdgesStepSafe w
      ⟨inBase, s.frontier⟩ count 0 ⟨s.mem, s.frontier + 4 * count⟩ ∧
    Memory.FramedTriple w s (initIndexedEdges inBase count) (8 * count + 1) ∅ fun outBase s' =>
      outBase = s.frontier ∧
      s'.frontier = s.frontier + 4 * count ∧
      Memory.WellFormed w s' ∧
      ∀ i < count,
        s'.mem (outBase + 4 * i) = s.mem (inBase + 3 * i) ∧
        s'.mem (outBase + 4 * i + 1) = s.mem (inBase + 3 * i + 1) ∧
        s'.mem (outBase + 4 * i + 2) = s.mem (inBase + 3 * i + 2) ∧
        s'.mem (outBase + 4 * i + 3) = i := by
  let S : Set ℕ := Set.Ico s.frontier (s.frontier + 4 * count)
  let inv (k a : ℕ) (t : Memory.State) : Prop :=
    a = k ∧ t.frontier = s.frontier + 4 * count ∧ Memory.WellFormed w t ∧
    (∀ x, x ∉ S → t.mem x = s.mem x) ∧
    ∀ i < k,
      t.mem (s.frontier + 4 * i) = s.mem (inBase + 3 * i) ∧
      t.mem (s.frontier + 4 * i + 1) = s.mem (inBase + 3 * i + 1) ∧
      t.mem (s.frontier + 4 * i + 2) = s.mem (inBase + 3 * i + 2) ∧
      t.mem (s.frontier + 4 * i + 3) = i
  have hfit_m1 : Fits w (count + 1) := by
    rcases count with _ | m
    · exact h16.of_le (by omega)
    · exact hfit.of_le (by omega)
  have hstep : ∀ k < count, ∀ a t, inv k a t →
      initIndexedEdgesStepSafe w (⟨inBase, s.frontier⟩, a) t ∧
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (initIndexedEdgesStep (⟨inBase, s.frontier⟩, a))) ∧
      let a' := (Memory.spec 0).clientResult t (initIndexedEdgesStep (⟨inBase, s.frontier⟩, a))
      let t' := (Memory.spec 0).clientState t (initIndexedEdgesStep (⟨inBase, s.frontier⟩, a))
      memoryCost (initIndexedEdgesStep (⟨inBase, s.frontier⟩, a)) t + 0 ≤ 0 + 7 ∧
      Memory.Modifies S t t' ∧
      inv (k + 1) a' t' := by
    intro k hk a t ⟨ha, htfr, hwt, hframe, hpref⟩
    subst a
    have hin_eq : ∀ q < 3, t.mem (inBase + 3 * k + q) = s.mem (inBase + 3 * k + q) :=
      fun q hq => hframe _ (by simp only [S, Set.mem_Ico, not_and, not_lt]; omega)
    have hfit_k1 : Fits w (k + 1) := hfit_m1.of_le (by omega)
    have hfit_k : Fits w k := hfit_k1.of_le (by omega)
    have hmem_t : ∀ a, Fits w (t.mem a) := hwt.mem_fits
    have hvh : (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (initIndexedEdgesStep (⟨inBase, s.frontier⟩, k))) := by
      dsimp only [initIndexedEdgesStep]
      valid_prog
      all_goals
        try dsimp only at *
        first
        | exact hmem_t _
        | omega
    have hcost : memoryCost (initIndexedEdgesStep (⟨inBase, s.frontier⟩, k)) t ≤ 7 := by
      dsimp only [initIndexedEdgesStep]
      prog_cost
    have hres : (Memory.spec 0).clientResult t (initIndexedEdgesStep (⟨inBase, s.frontier⟩, k)) =
        k + 1 := by
      dsimp only [initIndexedEdgesStep]
      simp only [clientResult_bind_read, clientResult_bind_write,
        StateTransitionSpec.clientResult_pure]
    have hst : (Memory.spec 0).clientState t (initIndexedEdgesStep (⟨inBase, s.frontier⟩, k)) =
        ⟨Function.update (Function.update (Function.update (Function.update t.mem
          (s.frontier + 4 * k) (t.mem (inBase + 3 * k)))
          (s.frontier + 4 * k + 1) (t.mem (inBase + 3 * k + 1)))
          (s.frontier + 4 * k + 2) (t.mem (inBase + 3 * k + 2)))
          (s.frontier + 4 * k + 3) k, t.frontier⟩ := by
      dsimp only [initIndexedEdgesStep]
      repeat rw [clientState_bind_read]
      rfl
    have hupd_out : ∀ x, x ∉ S →
        ((Memory.spec 0).clientState t (initIndexedEdgesStep (⟨inBase, s.frontier⟩, k))).mem x =
          t.mem x := by
      intro x hx
      rw [hst]
      simp only [S, Set.mem_Ico, not_and_or, not_le, not_lt] at hx
      update_simp
    refine ⟨⟨h16, hfit_k1⟩, hvh, by omega,
      ⟨by rw [hst], fun x _ hx => hupd_out x hx⟩,
      hres, by rw [hst]; exact htfr, wellFormed_clientState hwt hvh,
      fun x hx => (hupd_out x hx).trans (hframe x hx), fun i hi => ?_⟩
    rw [hst]; dsimp only
    by_cases hik : i = k
    · subst i
      have h0 := hin_eq 0 (by decide)
      have h1 := hin_eq 1 (by decide)
      have h2 := hin_eq 2 (by decide)
      simp only [Nat.add_zero] at h0
      refine ⟨?_, ?_, ?_, ?_⟩ <;> update_simp <;> simp [h0, h1, h2]
    · have hik' : i < k := by omega
      have hp := hpref i hik'
      refine ⟨?_, ?_, ?_, ?_⟩ <;> update_simp <;> simp [hp]
  obtain ⟨hsafe, hv_it, hm_it, hmod_it, _, hfr_it, hwf_it, _, hvals⟩ :=
    iterate_potential_spec initIndexedEdgesStep initIndexedEdgesStepSafe w ⟨inBase, s.frontier⟩
      7 count inv (fun _ _ _ => 0) S hstep 0 ⟨s.mem, s.frontier + 4 * count⟩
      ⟨rfl, rfl, ⟨hfit, hwf.mem_fits⟩, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  refine ⟨hsafe, ?_⟩
  have hprog : initIndexedEdges inBase count =
      (Memory.allocBlockDirty (4 * count) >>= fun out =>
        iterate initIndexedEdgesStep ⟨inBase, out.base⟩ count 0 >>= fun _ => pure out.base) := rfl
  rw [hprog]
  have ft_iter : Memory.FramedTriple w ⟨s.mem, s.frontier + 4 * count⟩
      (iterate initIndexedEdgesStep ⟨inBase, s.frontier⟩ count 0) (7 * count) S
      (fun _ s' => Memory.FramedTriple w s' (pure s.frontier) 0 S fun outBase s'' =>
        outBase = s.frontier ∧ s''.frontier = s.frontier + 4 * count ∧ Memory.WellFormed w s'' ∧
        ∀ i < count,
          s''.mem (outBase + 4 * i) = s.mem (inBase + 3 * i) ∧
          s''.mem (outBase + 4 * i + 1) = s.mem (inBase + 3 * i + 1) ∧
          s''.mem (outBase + 4 * i + 2) = s.mem (inBase + 3 * i + 2) ∧
          s''.mem (outBase + 4 * i + 3) = i) :=
    framedTriple_iff_realization.mpr ⟨hv_it, by simpa using hm_it, hmod_it,
      Memory.FramedTriple.pure ⟨rfl, hfr_it, hwf_it, hvals⟩⟩
  exact ((Memory.FramedTriple.allocBlockDirty_bind hfit
    (Memory.FramedTriple.bind_same ft_iter)).frame_empty_of_ge_frontier (S := S)
    fun _ ha => (Set.mem_Ico.mp ha).1).mono
    (by omega : 7 * count + 0 + 1 ≤ 8 * count + 1) fun _ _ h => h

/-- Uniform `Realizes .exact` certificate for `initIndexedEdges` with `work = 0`. -/
theorem realizes_initIndexedEdges :
    Realizes .exact (fun d : ℕ × ℕ => initIndexedEdges d.1 d.2)
      WordEncoding.encode WordEncoding.encode
      (fun w d s => Fits w 16 ∧ d.1 + 3 * d.2 ≤ s.frontier ∧ Fits w (s.frontier + 4 * d.2))
      (fun _ _ => 0) := by
  have hraw : Realizes .exact (fun d : ℕ × ℕ => initIndexedEdges d.1 d.2)
      WordEncoding.encode WordEncoding.encode
      (fun w d s => Fits w 16 ∧ Fits w (s.frontier + 4 * d.2) ∧
        iterationSafe (fun x : ((ℕ × ℕ) × Block) × ℕ =>
          let a := Prod.fst x
          initIndexedEdgesStep (⟨Prod.fst (Prod.fst a), (Prod.snd a).base⟩, Prod.snd x))
          (fun w x s =>
            let a := Prod.fst x
            initIndexedEdgesStepSafe w (⟨Prod.fst (Prod.fst a), (Prod.snd a).base⟩, Prod.snd x) s)
          w (d, ⟨s.frontier, 4 * d.2⟩) d.2 0 ⟨s.mem, s.frontier + 4 * d.2⟩)
      (fun _ _ => 0) := by
    unfold initIndexedEdges
    realize [realizes_allocBlockDirty, realizes_initIndexedEdgesStep]
    · exact h.2.1.of_le (by omega)
    · exact h.1.of_le (by decide)
    · exact iterationSafe_imp h.2.2 (fun _ => rfl) (fun _ _ hs => hs)
  refine hraw.consequence (fun w d s _ hmem ⟨h16, hin_lt, hfit⟩ => ?_) (fun _ _ => le_rfl)
  exact ⟨h16, hfit, iterationSafe_imp (initIndexedEdges_word_spec h16 hmem hin_lt hfit).1
    (fun _ => rfl) (fun _ _ hs => hs)⟩

/-- Framed specification for `initIndexedEdges`: copies `es` from stride-3 `inBase` into a fresh
stride-4 `IndexedEdge` array at `outBase = s.frontier` tagged with edge identifiers
`0 .. es.length - 1`, leaving all cells below `s.frontier` untouched, in at most `8 * es.length + 1`
memory operations. -/
theorem initIndexedEdges_spec {w n inBase : ℕ} {es : List (WeightedEdge n ℕ)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsEdges inBase es s.mem)
    (hin_lt : inBase + 3 * es.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + 4 * es.length)) :
    Memory.FramedTriple w s (initIndexedEdges inBase es.length) (8 * es.length + 1) ∅
      fun outBase s' =>
        outBase = s.frontier ∧
        s'.frontier = s.frontier + 4 * es.length ∧
        Memory.WellFormed w s' ∧
        HoldsIndexedEdges outBase (es.mapIdx fun i e => ⟨e.u, e.v, e.weight, i⟩) s'.mem := by
  refine (initIndexedEdges_word_spec h16 hwf hin_lt hfit).2.mono le_rfl
    fun outBase s' ⟨hout, hfr, hwf', hvals⟩ => ⟨hout, hfr, hwf', fun i hi => ?_⟩
  have hi_len : i < es.length := by simpa using hi
  obtain ⟨hu, hv, hw⟩ := hin i hi_len
  obtain ⟨h0, h1, h2, h3⟩ := hvals i hi_len
  simp only [List.getElem_mapIdx]
  exact ⟨h0.trans hu, h1.trans hv, h2.trans hw, h3⟩

/-! ## `emitMSFEdges` and `emitIndexedEdgesFromIdxs`: Index-Based Edge Emission -/

private structure EmitEdgeEnv where
  srcBase : ℕ
  selBase : ℕ
  outBase : ℕ

private word_enc_structure encEmitEdgeEnv : EmitEdgeEnv where
  srcBase : wordWords,
  selBase : wordWords,
  outBase : wordWords

private instance : WordEncoding EmitEdgeEnv := ⟨3, encEmitEdgeEnv⟩

private def emitEdgeStep (copyId : Bool) (x : EmitEdgeEnv × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst x
  let j := Prod.snd x
  let idx ← Memory.read (env.selBase + j)
  match copyId with
  | true =>
    let u ← Memory.read (env.srcBase + 4 * idx)
    let v ← Memory.read (env.srcBase + 4 * idx + 1)
    let wt ← Memory.read (env.srcBase + 4 * idx + 2)
    let eid ← Memory.read (env.srcBase + 4 * idx + 3)
    Memory.write (env.outBase + 4 * j) u
    Memory.write (env.outBase + 4 * j + 1) v
    Memory.write (env.outBase + 4 * j + 2) wt
    Memory.write (env.outBase + 4 * j + 3) eid
    pure (j + 1)
  | false =>
    let u ← Memory.read (env.srcBase + 3 * idx)
    let v ← Memory.read (env.srcBase + 3 * idx + 1)
    let wt ← Memory.read (env.srcBase + 3 * idx + 2)
    Memory.write (env.outBase + 1 + 3 * j) u
    Memory.write (env.outBase + 1 + 3 * j + 1) v
    Memory.write (env.outBase + 1 + 3 * j + 2) wt
    pure (j + 1)

private def emitEdgeStepSafe (w : ℕ) (x : EmitEdgeEnv × ℕ) (_ : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (Prod.snd x + 1)

private theorem realizes_emitEdgeStep_history (copyId : Bool) : Realizes .exact
    (emitEdgeStep copyId) (appendWords encEmitEdgeEnv wordWords) wordWords
    (fun w d s => emitEdgeStepSafe w d s ∧
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (emitEdgeStep copyId d)))
    (fun _ _ => 0) := by
  cases copyId <;>
  · unfold emitEdgeStep
    dsimp only
    realize
    all_goals
      obtain ⟨⟨h16, hfit⟩, hv⟩ := h
      have hfront := hmem.frontier_fits
      dsimp only [StateTransitionSpec.clientHistory] at hv
      simp_all only [StateTransitionSpec.runClient_lift_bind',
        StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
        Memory.write, Memory.step_read, Memory.step_write, Memory.valid]
    all_goals fits

private theorem realizes_emitEdgeStep (copyId : Bool) : Realizes .exact
    (emitEdgeStep copyId) (appendWords encEmitEdgeEnv wordWords) wordWords
    emitEdgeStepSafe (fun _ _ => 0) :=
  (realizes_emitEdgeStep_history copyId).consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

private abbrev emitDstOff (b : Bool) : ℕ := cond b 0 1

private abbrev emitStride (b : Bool) : ℕ := cond b 4 3

private abbrev emitStepCost (b : Bool) : ℕ := cond b 9 7

private theorem emitEdgeStep_iterate_framed (copyId : Bool) {w : ℕ}
    (srcBase selBase outBase count : ℕ) {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s) (hfit_cnt : Fits w (count + 1))
    (hdst_le : outBase + emitDstOff copyId + emitStride copyId * count ≤ s.frontier)
    (hsel_lt : selBase + count ≤ s.frontier)
    (hsel_disj : ∀ j < count, selBase + j ∉
      Set.Ico (outBase + emitDstOff copyId)
        (outBase + emitDstOff copyId + emitStride copyId * count))
    (hsrc_lt : ∀ j < count,
      srcBase + emitStride copyId * s.mem (selBase + j) + emitStride copyId ≤ s.frontier)
    (hsrc_disj : ∀ j < count, ∀ q < emitStride copyId,
      srcBase + emitStride copyId * s.mem (selBase + j) + q ∉
        Set.Ico (outBase + emitDstOff copyId)
          (outBase + emitDstOff copyId + emitStride copyId * count)) :
    let S := Set.Ico (outBase + emitDstOff copyId)
      (outBase + emitDstOff copyId + emitStride copyId * count)
    iterationSafe (emitEdgeStep copyId) emitEdgeStepSafe w ⟨srcBase, selBase, outBase⟩ count 0 s ∧
    Memory.FramedTriple w s (iterate (emitEdgeStep copyId) ⟨srcBase, selBase, outBase⟩ count 0)
      (emitStepCost copyId * count) S fun _ s' =>
        s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        ∀ j < count, ∀ q < emitStride copyId,
          s'.mem (outBase + emitDstOff copyId + emitStride copyId * j + q) =
            s.mem (srcBase + emitStride copyId * s.mem (selBase + j) + q) := by
  let S := Set.Ico (outBase + emitDstOff copyId)
    (outBase + emitDstOff copyId + emitStride copyId * count)
  let inv (k a : ℕ) (t : Memory.State) : Prop :=
    a = k ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t ∧
    (∀ x, x ∉ S → t.mem x = s.mem x) ∧
    ∀ j < k, ∀ q < emitStride copyId,
      t.mem (outBase + emitDstOff copyId + emitStride copyId * j + q) =
        s.mem (srcBase + emitStride copyId * s.mem (selBase + j) + q)
  have hstep : ∀ k < count, ∀ a t, inv k a t →
      emitEdgeStepSafe w (⟨srcBase, selBase, outBase⟩, a) t ∧
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t
          (emitEdgeStep copyId (⟨srcBase, selBase, outBase⟩, a))) ∧
      let a' := (Memory.spec 0).clientResult t
        (emitEdgeStep copyId (⟨srcBase, selBase, outBase⟩, a))
      let t' := (Memory.spec 0).clientState t
        (emitEdgeStep copyId (⟨srcBase, selBase, outBase⟩, a))
      memoryCost (emitEdgeStep copyId (⟨srcBase, selBase, outBase⟩, a)) t + 0 ≤
        0 + emitStepCost copyId ∧
      Memory.Modifies S t t' ∧
      inv (k + 1) a' t' := by
    intro k hk a t ⟨ha, htfr, hwt, hframe, hpref⟩
    subst a
    have hsel_eq : t.mem (selBase + k) = s.mem (selBase + k) := hframe _ (hsel_disj k hk)
    have hsrc_le := hsrc_lt k hk
    have hsrc_eq : ∀ q < emitStride copyId,
        t.mem (srcBase + emitStride copyId * s.mem (selBase + k) + q) =
          s.mem (srcBase + emitStride copyId * s.mem (selBase + k) + q) :=
      fun q hq => hframe _ (hsrc_disj k hk q hq)
    have hfit_k1 : Fits w (k + 1) := hfit_cnt.of_le (by omega)
    have hft : Memory.FramedTriple w t (emitEdgeStep copyId (⟨srcBase, selBase, outBase⟩, k))
        (emitStepCost copyId) S fun a' t' =>
          a' = k + 1 ∧ t'.frontier = s.frontier ∧ Memory.WellFormed w t' ∧
          ∀ j < k + 1, ∀ q < emitStride copyId,
            t'.mem (outBase + emitDstOff copyId + emitStride copyId * j + q) =
              s.mem (srcBase + emitStride copyId * s.mem (selBase + j) + q) := by
      cases copyId
      all_goals
        dsimp only [emitEdgeStep, emitDstOff, emitStride, emitStepCost, cond, S] at *
        have htmem := hwt.mem_fits
        repeat
          first
          | refine Memory.FramedTriple.read_bind ?_ ?_
            focus ((try rw [hsel_eq]); omega)
          | refine Memory.FramedTriple.write_bind_of_mem ?_ (htmem _) (Set.mem_Ico.mpr ⟨?_, ?_⟩) ?_
            focus ((try dsimp only); omega)
            focus omega
            focus omega
        apply Memory.FramedTriple.pure
        refine ⟨rfl, htfr, ?_, fun j hj q hq => ?_⟩
        · refine ⟨htfr ▸ hwf.frontier_fits, fun z => ?_⟩
          simp only [Function.update_apply]
          split_ifs <;> exact htmem _
        · by_cases hjk : j = k
          · subst j
            have h0 := hsrc_eq 0 (by omega)
            have h1 := hsrc_eq 1 (by omega)
            have h2 := hsrc_eq 2 (by omega)
            try have h3 := hsrc_eq 3 (by omega)
            rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;>
              first | omega | (update_simp; simp_all)
          · have hp := hpref j (by omega) q hq
            update_simp; exact hp
    obtain ⟨hv_st, hm_st, hmod_st, hres_st, hfr_st, hww_st, hvals_st⟩ :=
      framedTriple_iff_realization.mp hft
    have hfr_w : ((Memory.spec w).clientState t
        (emitEdgeStep copyId (⟨srcBase, selBase, outBase⟩, k))).frontier = t.frontier := by
      rw [clientState_width]; exact hfr_st.trans htfr.symm
    exact ⟨⟨h16, hfit_k1⟩, hv_st, by omega, hmod_st, hres_st, hfr_st, hww_st,
      fun x hx => by
        rw [← clientState_width w]
        exact (hft.mem_eq_of_frontier_eq hfr_w x hx).trans (hframe x hx),
      hvals_st⟩
  obtain ⟨hsafe, hv_it, hm_it, hmod_it, _, hfr_it, hwf_it, _, hvals⟩ :=
    iterate_potential_spec (emitEdgeStep copyId) emitEdgeStepSafe w ⟨srcBase, selBase, outBase⟩
      (emitStepCost copyId) count inv (fun _ _ _ => 0) S hstep 0 s
      ⟨rfl, rfl, hwf, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  exact ⟨hsafe, framedTriple_iff_realization.mpr ⟨hv_it, by simpa using hm_it, hmod_it,
    hfr_it, hwf_it, hvals⟩⟩

/-- Materialize `d.count` selected raw edges (`d = { srcBase, selBase, count }`) from
stride-3 `d.srcBase` and indices at `d.selBase` into a length-prefixed `Kruskal.encodeEdges`
output array, returning its base address. -/
def emitMSFEdges (d : SelectedEdgesArgs) : Memory.Prog ℕ := do
  let out ← Memory.allocBlockDirty (3 * d.count + 1)
  Memory.write out.base (3 * d.count)
  let _ ← iterate (emitEdgeStep false) ⟨d.srcBase, d.selBase, out.base⟩ d.count 0
  pure out.base

private theorem emitMSFEdges_word_spec {w : ℕ} {d : SelectedEdgesArgs} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hsel_lt : d.selBase + d.count ≤ s.frontier)
    (hfit : Fits w (s.frontier + (3 * d.count + 1)))
    (hsrc_lt : ∀ j < d.count, d.srcBase + 3 * s.mem (d.selBase + j) + 3 ≤ s.frontier) :
    iterationSafe (emitEdgeStep false) emitEdgeStepSafe w ⟨d.srcBase, d.selBase, s.frontier⟩
      d.count 0 ⟨Function.update s.mem s.frontier (3 * d.count), s.frontier + (3 * d.count + 1)⟩ ∧
    Memory.FramedTriple w s (emitMSFEdges d) (8 * d.count + 4) ∅ fun outBase s' =>
      outBase = s.frontier ∧
      s'.frontier = s.frontier + (3 * d.count + 1) ∧
      Memory.WellFormed w s' ∧
      s'.mem outBase = 3 * d.count ∧
      ∀ j < d.count, ∀ q < 3,
        s'.mem (outBase + 1 + 3 * j + q) = s.mem (d.srcBase + 3 * s.mem (d.selBase + j) + q) := by
  let S : Set ℕ := Set.Ico (s.frontier + 1) (s.frontier + 1 + 3 * d.count)
  let S₀ : Set ℕ := Set.Ico s.frontier (s.frontier + (3 * d.count + 1))
  let s₁ : Memory.State :=
    ⟨Function.update s.mem s.frontier (3 * d.count), s.frontier + (3 * d.count + 1)⟩
  have hfit_cnt : Fits w (d.count + 1) := hfit.of_le (by omega)
  have hfit_3cnt : Fits w (3 * d.count) := hfit.of_le (by omega)
  have hwf₁ : Memory.WellFormed w s₁ := by
    refine ⟨hfit, fun a => ?_⟩
    by_cases ha : a = s.frontier <;> simp only [s₁, Function.update_apply, ha, ↓reduceIte]
    · exact hfit_3cnt
    · exact hwf.mem_fits a
  have hs₁_sel : ∀ j < d.count, s₁.mem (d.selBase + j) = s.mem (d.selBase + j) := fun j hj => by
    simp only [s₁, Function.update_of_ne (by omega : d.selBase + j ≠ s.frontier)]
  have hs₁_src : ∀ j < d.count, ∀ q < 3,
      s₁.mem (d.srcBase + 3 * s.mem (d.selBase + j) + q) =
        s.mem (d.srcBase + 3 * s.mem (d.selBase + j) + q) := fun j hj q hq => by
    have := hsrc_lt j hj
    simp only [s₁, Function.update_of_ne (by omega : d.srcBase + 3 * s.mem (d.selBase + j) + q ≠
      s.frontier)]
  obtain ⟨hsafe, hft_it⟩ := emitEdgeStep_iterate_framed false d.srcBase d.selBase s.frontier d.count
    h16 hwf₁ hfit_cnt
    (by dsimp only [s₁, emitDstOff, emitStride, cond]; omega) (by dsimp only [s₁]; omega)
    (fun j hj => by simp only [Set.mem_Ico, emitDstOff, emitStride, cond, not_and, not_lt]; omega)
    (fun j hj => by
      rw [hs₁_sel j hj]; have := hsrc_lt j hj
      dsimp only [s₁, emitStride, cond]; omega)
    (fun j hj q hq => by
      rw [hs₁_sel j hj]; have := hsrc_lt j hj
      simp only [Set.mem_Ico, emitDstOff, emitStride, cond, not_and, not_lt] at hq ⊢; omega)
  refine ⟨hsafe, ?_⟩
  have hprog : emitMSFEdges d =
      (Memory.allocBlockDirty (3 * d.count + 1) >>= fun out =>
        Memory.write out.base (3 * d.count) >>= fun _ =>
          iterate (emitEdgeStep false) ⟨d.srcBase, d.selBase, out.base⟩ d.count 0 >>= fun _ =>
            pure out.base) := rfl
  rw [hprog]
  have hiter_ft : Memory.FramedTriple w s₁
      (iterate (emitEdgeStep false) ⟨d.srcBase, d.selBase, s.frontier⟩ d.count 0) (7 * d.count) S
      fun _ s' => Memory.FramedTriple w s' (pure s.frontier) 0 S fun outBase s'' =>
        outBase = s.frontier ∧ s''.frontier = s.frontier + (3 * d.count + 1) ∧
        Memory.WellFormed w s'' ∧ s''.mem outBase = 3 * d.count ∧
        ∀ j < d.count, ∀ q < 3,
          s''.mem (outBase + 1 + 3 * j + q) =
            s.mem (d.srcBase + 3 * s.mem (d.selBase + j) + q) := by
    refine Memory.Triple.mono hft_it le_rfl fun _ t' ⟨hm, hfr', hwt', hvals⟩ =>
      ⟨hm, Memory.FramedTriple.pure ⟨rfl, hfr', hwt', ?_, fun j hj q hq => ?_⟩⟩
    · have hout_mem : t'.mem s.frontier = s₁.mem s.frontier :=
        hm.mem_eq_of_not_mem (by dsimp only [s₁]; omega)
          (by simp only [Set.mem_Ico, emitDstOff, emitStride, cond, not_and, not_lt]; omega)
      simpa [s₁, Function.update_self] using hout_mem
    · have hv := hvals j hj q hq
      dsimp only [emitDstOff, emitStride, cond] at hv
      rwa [hs₁_sel j hj, hs₁_src j hj q hq] at hv
  let s₀ : Memory.State := ⟨s.mem, s.frontier + (3 * d.count + 1)⟩
  have hft_wr : Memory.FramedTriple w s₀
      (Memory.write s.frontier (3 * d.count) >>= fun _ =>
        iterate (emitEdgeStep false) ⟨d.srcBase, d.selBase, s.frontier⟩ d.count 0 >>= fun _ =>
          pure s.frontier)
      (7 * d.count + 0 + 1) S₀ fun outBase s' =>
        outBase = s.frontier ∧ s'.frontier = s.frontier + (3 * d.count + 1) ∧
        Memory.WellFormed w s' ∧ s'.mem outBase = 3 * d.count ∧
        ∀ j < d.count, ∀ q < 3,
          s'.mem (outBase + 1 + 3 * j + q) =
            s.mem (d.srcBase + 3 * s.mem (d.selBase + j) + q) :=
    Memory.FramedTriple.write_bind_of_mem (S := S₀) (by dsimp only [s₀]; omega) hfit_3cnt
      (by simp only [S₀, Set.mem_Ico]; omega)
      ((Memory.FramedTriple.bind_same hiter_ft).frame_mono (S' := S₀) fun x hx => by
        simp only [S, S₀, Set.mem_Ico] at hx ⊢; omega)
  exact ((Memory.FramedTriple.allocBlockDirty_bind hfit hft_wr).frame_empty_of_ge_frontier (S := S₀)
    fun _ ha => (Set.mem_Ico.mp ha).1).mono
    (by omega : 7 * d.count + 0 + 1 + 1 ≤ 8 * d.count + 4) fun _ _ h => h

/-- Uniform `Realizes .exact` certificate for `emitMSFEdges` with `work = 0`. -/
theorem realizes_emitMSFEdges :
    Realizes .exact emitMSFEdges WordEncoding.encode WordEncoding.encode
      (fun w d s => Fits w 16 ∧ d.selBase + d.count ≤ s.frontier ∧
        Fits w (s.frontier + (3 * d.count + 1)) ∧
        ∀ j < d.count, d.srcBase + 3 * s.mem (d.selBase + j) + 3 ≤ s.frontier)
      (fun _ _ => 0) := by
  have hraw : Realizes .exact emitMSFEdges WordEncoding.encode WordEncoding.encode
      (fun w d s => Fits w 16 ∧ Fits w (s.frontier + (3 * d.count + 1)) ∧
        iterationSafe (fun x : ((SelectedEdgesArgs × Block) × Unit) × ℕ =>
          let a := Prod.fst (Prod.fst x)
          emitEdgeStep false (⟨(Prod.fst a).srcBase, (Prod.fst a).selBase, (Prod.snd a).base⟩,
            Prod.snd x))
          (fun w x s =>
            let a := Prod.fst (Prod.fst x)
            emitEdgeStepSafe w (⟨(Prod.fst a).srcBase, (Prod.fst a).selBase, (Prod.snd a).base⟩,
              Prod.snd x) s)
          w ((d, ⟨s.frontier, 3 * d.count + 1⟩), ()) d.count 0
          ⟨Function.update s.mem s.frontier (3 * d.count), s.frontier + (3 * d.count + 1)⟩)
      (fun _ _ => 0) := by
    unfold emitMSFEdges
    realize [realizes_allocBlockDirty, realizes_emitEdgeStep false]
    · exact h.2.1.of_le (by omega)
    · exact h.1.of_le (by decide)
    · exact h.2.1.of_le (by omega)
    · exact iterationSafe_imp h.2.2 (fun _ => rfl) (fun _ _ hs => hs)
  refine hraw.consequence (fun w d s _ hmem ⟨h16, hsel_lt, hfit, hsrc_lt⟩ => ?_)
    (fun _ _ => le_rfl)
  exact ⟨h16, hfit, iterationSafe_imp
    (emitMSFEdges_word_spec h16 hmem hsel_lt hfit hsrc_lt).1
    (fun _ => rfl) (fun _ _ hs => hs)⟩

/-- Framed specification for `emitMSFEdges`: materializes `selIds.map fun i => es[i.val]` as a
length-prefixed `Kruskal.encodeEdges` array at `outBase = s.frontier` leaving all cells below
`s.frontier` untouched, in at most `8 * selIds.length + 4` memory operations. -/
theorem emitMSFEdges_spec {w n : ℕ} {d : SelectedEdgesArgs}
    {es : List (WeightedEdge n ℕ)} {selIds : List (Fin es.length)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsEdges d.srcBase es s.mem)
    (hin_lt : d.srcBase + 3 * es.length ≤ s.frontier)
    (hsel : ∀ j (hj : j < selIds.length), s.mem (d.selBase + j) = selIds[j].val)
    (hsel_lt : d.selBase + d.count ≤ s.frontier)
    (hcnt : d.count = selIds.length)
    (hfit : Fits w (s.frontier + (3 * d.count + 1))) :
    Memory.FramedTriple w s (emitMSFEdges d) (8 * d.count + 4) ∅
      fun outBase s' =>
        outBase = s.frontier ∧
        s'.frontier = s.frontier + (3 * d.count + 1) ∧
        Memory.WellFormed w s' ∧
        outputList s'.mem outBase = Kruskal.encodeEdges (selIds.map fun i => es[i.val]) := by
  have hsrc_lt : ∀ j < d.count, d.srcBase + 3 * s.mem (d.selBase + j) + 3 ≤ s.frontier := by
    intro j hj
    have hj' : j < selIds.length := hcnt ▸ hj
    rw [hsel j hj']
    have := selIds[j].isLt
    omega
  refine (emitMSFEdges_word_spec h16 hwf hsel_lt hfit hsrc_lt).2.mono le_rfl
    fun outBase s' ⟨hout, hfr, hwf', hhdr, hvals⟩ => ⟨hout, hfr, hwf', ?_⟩
  let outEs := selIds.map fun i => es[i.val]
  have hholds : HoldsEdges (s.frontier + 1) outEs s'.mem := by
    intro j hj
    have hj' : j < selIds.length := by simpa [outEs] using hj
    have hsel_j : s.mem (d.selBase + j) = selIds[j].val := hsel j hj'
    obtain ⟨hu, hv, hw⟩ := hin selIds[j].val selIds[j].isLt
    have hv0 : s'.mem (s.frontier + 1 + 3 * j) = es[selIds[j].val].u.val := by
      have h := hvals j (hcnt ▸ hj') 0 (by decide)
      rw [hout, hsel_j] at h
      simpa using h.trans hu
    have hv1 : s'.mem (s.frontier + 1 + 3 * j + 1) = es[selIds[j].val].v.val := by
      have h := hvals j (hcnt ▸ hj') 1 (by decide)
      rw [hout, hsel_j] at h
      simpa using h.trans hv
    have hv2 : s'.mem (s.frontier + 1 + 3 * j + 2) = es[selIds[j].val].weight := by
      have h := hvals j (hcnt ▸ hj') 2 (by decide)
      rw [hout, hsel_j] at h
      simpa using h.trans hw
    simpa [outEs] using ⟨hv0, hv1, hv2⟩
  rw [hout] at hhdr ⊢
  exact outputList_eq_iff.mpr
    ⟨by rw [hhdr, hcnt, length_encodeEdges]; simp, holdsList_of_holdsEdges hholds⟩

/-- Materialize `d.count` selected stride-4 `IndexedEdge` records (`d : SelectedEdgesArgs`)
from `d.srcBase` and indices at `d.selBase` into a fresh stride-4 `IndexedEdge` array, preserving
original edge identifiers and returning its base address. -/
def emitIndexedEdgesFromIdxs (d : SelectedEdgesArgs) : Memory.Prog ℕ := do
  let out ← Memory.allocBlockDirty (4 * d.count)
  let _ ← iterate (emitEdgeStep true) ⟨d.srcBase, d.selBase, out.base⟩ d.count 0
  pure out.base

private theorem emitIndexedEdgesFromIdxs_word_spec {w : ℕ} {d : SelectedEdgesArgs}
    {s : Memory.State} (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hsel_lt : d.selBase + d.count ≤ s.frontier)
    (hfit : Fits w (s.frontier + 4 * d.count))
    (hsrc_lt : ∀ j < d.count, d.srcBase + 4 * s.mem (d.selBase + j) + 4 ≤ s.frontier) :
    iterationSafe (emitEdgeStep true) emitEdgeStepSafe w ⟨d.srcBase, d.selBase, s.frontier⟩
      d.count 0 ⟨s.mem, s.frontier + 4 * d.count⟩ ∧
    Memory.FramedTriple w s (emitIndexedEdgesFromIdxs d) (9 * d.count + 1) ∅ fun outBase s' =>
      outBase = s.frontier ∧
      s'.frontier = s.frontier + 4 * d.count ∧
      Memory.WellFormed w s' ∧
      ∀ j < d.count, ∀ q < 4,
        s'.mem (outBase + 4 * j + q) = s.mem (d.srcBase + 4 * s.mem (d.selBase + j) + q) := by
  let S : Set ℕ := Set.Ico s.frontier (s.frontier + 4 * d.count)
  have hfit_cnt : Fits w (d.count + 1) := by
    rcases Nat.eq_zero_or_pos d.count with h0 | hpos
    · rw [h0]; exact h16.of_le (by decide)
    · exact hfit.of_le (by omega)
  have hwf₁ : Memory.WellFormed w ⟨s.mem, s.frontier + 4 * d.count⟩ := ⟨hfit, hwf.mem_fits⟩
  obtain ⟨hsafe, hft_it⟩ := emitEdgeStep_iterate_framed true d.srcBase d.selBase s.frontier d.count
    h16 hwf₁ hfit_cnt
    (by dsimp only [emitDstOff, emitStride, cond]; omega) (by dsimp only; omega)
    (fun j hj => by simp only [Set.mem_Ico, emitDstOff, emitStride, cond, not_and, not_lt]; omega)
    (fun j hj => by have := hsrc_lt j hj; dsimp only [emitStride, cond]; omega)
    (fun j hj q hq => by
      have := hsrc_lt j hj
      simp only [Set.mem_Ico, emitDstOff, emitStride, cond, not_and, not_lt] at hq ⊢; omega)
  refine ⟨hsafe, ?_⟩
  have hprog : emitIndexedEdgesFromIdxs d =
      (Memory.allocBlockDirty (4 * d.count) >>= fun out =>
        iterate (emitEdgeStep true) ⟨d.srcBase, d.selBase, out.base⟩ d.count 0 >>= fun _ =>
          pure out.base) := rfl
  rw [hprog]
  have hiter_ft : Memory.FramedTriple w ⟨s.mem, s.frontier + 4 * d.count⟩
      (iterate (emitEdgeStep true) ⟨d.srcBase, d.selBase, s.frontier⟩ d.count 0) (9 * d.count) S
      fun _ s' => Memory.FramedTriple w s' (pure s.frontier) 0 S fun outBase s'' =>
        outBase = s.frontier ∧ s''.frontier = s.frontier + 4 * d.count ∧
        Memory.WellFormed w s'' ∧
        ∀ j < d.count, ∀ q < 4,
          s''.mem (outBase + 4 * j + q) = s.mem (d.srcBase + 4 * s.mem (d.selBase + j) + q) :=
    hft_it.mono le_rfl fun _ _ ⟨hfr', hwt', hvals⟩ =>
      Memory.FramedTriple.pure ⟨rfl, hfr', hwt', fun j hj q hq => by
        simpa [emitDstOff, emitStride, cond] using hvals j hj q hq⟩
  exact ((Memory.FramedTriple.allocBlockDirty_bind hfit
    (Memory.FramedTriple.bind_same hiter_ft)).frame_empty_of_ge_frontier (S := S)
    fun _ ha => (Set.mem_Ico.mp ha).1).mono
    (by omega : 9 * d.count + 0 + 1 ≤ 9 * d.count + 1) fun _ _ h => h

/-- Uniform `Realizes .exact` certificate for `emitIndexedEdgesFromIdxs` with `work = 0`. -/
theorem realizes_emitIndexedEdgesFromIdxs :
    Realizes .exact emitIndexedEdgesFromIdxs WordEncoding.encode WordEncoding.encode
      (fun w d s => Fits w 16 ∧ d.selBase + d.count ≤ s.frontier ∧
        Fits w (s.frontier + 4 * d.count) ∧
        ∀ j < d.count, d.srcBase + 4 * s.mem (d.selBase + j) + 4 ≤ s.frontier)
      (fun _ _ => 0) := by
  have hraw : Realizes .exact emitIndexedEdgesFromIdxs WordEncoding.encode WordEncoding.encode
      (fun w d s => Fits w 16 ∧ Fits w (s.frontier + 4 * d.count) ∧
        iterationSafe (fun x : (SelectedEdgesArgs × Block) × ℕ =>
          let a := Prod.fst x
          emitEdgeStep true (⟨(Prod.fst a).srcBase, (Prod.fst a).selBase, (Prod.snd a).base⟩,
            Prod.snd x))
          (fun w x s =>
            let a := Prod.fst x
            emitEdgeStepSafe w (⟨(Prod.fst a).srcBase, (Prod.fst a).selBase, (Prod.snd a).base⟩,
              Prod.snd x) s)
          w (d, ⟨s.frontier, 4 * d.count⟩) d.count 0 ⟨s.mem, s.frontier + 4 * d.count⟩)
      (fun _ _ => 0) := by
    unfold emitIndexedEdgesFromIdxs
    realize [realizes_allocBlockDirty, realizes_emitEdgeStep true]
    · exact h.2.1.of_le (by omega)
    · exact h.1.of_le (by decide)
    · exact iterationSafe_imp h.2.2 (fun _ => rfl) (fun _ _ hs => hs)
  refine hraw.consequence (fun w d s _ hmem ⟨h16, hsel_lt, hfit, hsrc_lt⟩ => ?_)
    (fun _ _ => le_rfl)
  exact ⟨h16, hfit, iterationSafe_imp
    (emitIndexedEdgesFromIdxs_word_spec h16 hmem hsel_lt hfit hsrc_lt).1
    (fun _ => rfl) (fun _ _ hs => hs)⟩

/-- Framed specification for `emitIndexedEdgesFromIdxs`: materializes `idxs.map fun i => es[i.val]`
into a fresh stride-4 `IndexedEdge` array at `outBase = s.frontier` leaving all cells below
`s.frontier` untouched, in at most `9 * idxs.length + 1` memory operations. -/
theorem emitIndexedEdgesFromIdxs_spec {w n : ℕ} {d : SelectedEdgesArgs}
    {es : List (IndexedEdge n)} {idxs : List (Fin es.length)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges d.srcBase es s.mem)
    (hin_lt : d.srcBase + 4 * es.length ≤ s.frontier)
    (hsel : ∀ j (hj : j < idxs.length), s.mem (d.selBase + j) = idxs[j].val)
    (hsel_lt : d.selBase + d.count ≤ s.frontier)
    (hcnt : d.count = idxs.length)
    (hfit : Fits w (s.frontier + 4 * d.count)) :
    Memory.FramedTriple w s (emitIndexedEdgesFromIdxs d) (9 * d.count + 1) ∅
      fun outBase s' =>
        outBase = s.frontier ∧
        s'.frontier = s.frontier + 4 * d.count ∧
        Memory.WellFormed w s' ∧
        HoldsIndexedEdges outBase (idxs.map fun i => es[i.val]) s'.mem := by
  have hsrc_lt : ∀ j < d.count, d.srcBase + 4 * s.mem (d.selBase + j) + 4 ≤ s.frontier := by
    intro j hj
    have hj' : j < idxs.length := hcnt ▸ hj
    rw [hsel j hj']
    have := idxs[j].isLt
    omega
  refine (emitIndexedEdgesFromIdxs_word_spec h16 hwf hsel_lt hfit hsrc_lt).2.mono le_rfl
    fun outBase s' ⟨hout, hfr, hwf', hvals⟩ => ⟨hout, hfr, hwf', fun j hj => ?_⟩
  have hj' : j < idxs.length := by simpa using hj
  have hsel_j : s.mem (d.selBase + j) = idxs[j].val := hsel j hj'
  obtain ⟨hu, hv, hw, hid⟩ := hin idxs[j].val idxs[j].isLt
  have hq : ∀ q < 4, s'.mem (outBase + 4 * j + q) = s.mem (d.srcBase + 4 * idxs[j].val + q) :=
    fun q hq => by have hv' := hvals j (hcnt ▸ hj') q hq; rwa [hsel_j] at hv'
  simp only [List.getElem_map]
  exact ⟨(hq 0 (by decide)).trans hu, (hq 1 (by decide)).trans hv,
    (hq 2 (by decide)).trans hw, (hq 3 (by decide)).trans hid⟩

end Cslib.Algorithms.WordRAM.MinimumSpanningForest
