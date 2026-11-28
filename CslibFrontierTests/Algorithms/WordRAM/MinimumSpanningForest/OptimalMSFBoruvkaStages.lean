/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (tests for OptimalMSF Boruvka stages)

import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSF.BoruvkaStages
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsTestSupport

/-!
# Tests for Optimal MSF Preprocessing and 3-Stage Borůvka Contraction

Exercises `MSFLiftInv`, `MSFLiftInv.sum_le`, `initPreprocessProg`, and `boruvkaThreeStageProg`
across:

1. Empty-edge (`m = 0, n = 0` and `m = 0, n = 4`) and all-self-loop raw graph boundaries.
2. Multigraph preprocessing (`initPreprocessProg_spec`) eliminating self-loops, parallel heavier
   edges, and isolated vertices while preserving `IsSimple` and `MSFLiftInv`.
3. Non-empty 3-stage Borůvka contraction on a 9-vertex cyclic graph verifying `8x` vertex
   reduction (`8 * res.numVertices ≤ nCur`), `MSFLiftInv.sum_le`, selection array writes,
   non-empty initial `accIds` preservation, and full `MSFLiftInv` MSF lifting back to
   `IsMinSpanningForest`.
4. Composite `Realizes .exact` pipeline (`initAndBoruvkaThreeProg` via `realize`) and lowering to a
   width-blind deterministic `Program .standard` via
   `exists_standard_basis_init_program_state_from_words`.
-/

-- This test module intentionally exports no declarations.
set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSFBoruvkaStages

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Algorithms.WordRAM.Kruskal
open Cslib.Query.MinimumSpanningForest
open Cslib.Algorithms.WordRAM.MinimumSpanningForest
open CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsTestSupport

/-! ## Private setup and MSF witnesses -/

private theorem eq_nil_of_isSimple_of_le_one {n : ℕ} (hn : n ≤ 1)
    (es : List (IndexedEdge n)) (hs : IsSimple (edgeEnds (es.map IndexedEdge.toWeighted))) :
    es = [] := by
  cases es with
  | nil => rfl
  | cons e rest =>
    exfalso
    have hdiag : ¬ (edgeEnds (IndexedEdge.toWeighted e ::
        rest.map IndexedEdge.toWeighted) ⟨0, by simp⟩).IsDiag :=
      ((isSimple_iff _).mp hs).1 ⟨0, by simp⟩
    have heq : e.u = e.v := Fin.ext (by have := e.u.isLt; have := e.v.isLt; omega)
    have hmk : edgeEnds (IndexedEdge.toWeighted e :: rest.map IndexedEdge.toWeighted)
        ⟨0, by simp⟩ = s(e.u, e.u) := by
      simp [edgeEnds, IndexedEdge.toWeighted, heq]
    rw [hmk] at hdiag
    exact hdiag (by simp)

private def mkRawInitState {n : ℕ} (es : List (WeightedEdge n ℕ)) : Memory.State :=
  mkInitStateFromWords (encodeEdges es)

private theorem mkRawInitState_spec {w n : ℕ} (es : List (WeightedEdge n ℕ))
    (hn : Fits w n) (h3m : Fits w (3 * es.length)) (hwts : ∀ e ∈ es, Fits w e.weight) :
    Memory.WellFormed w (mkRawInitState es) ∧
    (mkRawInitState es).frontier = 3 * es.length ∧
    HoldsEdges 0 es (mkRawInitState es).mem := by
  have hwf0 : Memory.WellFormed w ⟨fun _ => 0, 0⟩ :=
    ⟨Nat.two_pow_pos w, fun _ => Nat.two_pow_pos w⟩
  have hfit : Fits w ((⟨fun _ => 0, 0⟩ : Memory.State).frontier + (encodeEdges es).length) := by
    simpa [length_encodeEdges] using h3m
  have hwords : ∀ v ∈ encodeEdges es, Fits w v := by
    clear hfit h3m
    revert hwts
    induction es with
    | nil => intro _ v hv; simp [encodeEdges] at hv
    | cons e tl ih =>
      intro hwts v hv
      rw [encodeEdges_cons] at hv
      simp only [List.mem_cons] at hv
      rcases hv with rfl | rfl | rfl | hv'
      · exact hn.of_le (le_of_lt e.u.isLt)
      · exact hn.of_le (le_of_lt e.v.isLt)
      · exact hwts e List.mem_cons_self
      · exact ih (fun x hx => hwts x (List.mem_cons_of_mem e hx)) v hv'
  have hft := initFromWordsProg_spec hwf0 hfit hwords
  obtain ⟨_, _, _, hb, hfr, hhold, hwf'⟩ := framedTriple_iff_realization.mp hft
  refine ⟨hwf', ?_, ?_⟩
  · simpa [mkRawInitState, mkInitStateFromWords, length_encodeEdges] using hfr
  · rw [hb] at hhold
    exact holdsEdges_of_holdsList hhold

private def mkStageState {n : ℕ} (es : List (IndexedEdge n)) (extra : ℕ) : Memory.State :=
  ⟨(mkInitState es).mem, 4 * es.length + extra⟩

private theorem mkStageState_spec {w n : ℕ} (es : List (IndexedEdge n)) {extra : ℕ}
    (hn : Fits w n) (hfr_fit : Fits w (4 * es.length + extra))
    (hwts : ∀ e ∈ es, Fits w e.weight ∧ Fits w e.id) :
    Memory.WellFormed w (mkStageState es extra) ∧
    (mkStageState es extra).frontier = 4 * es.length + extra ∧
    HoldsIndexedEdges 0 es (mkStageState es extra).mem := by
  obtain ⟨hwf, _, hin⟩ := mkInitState_spec (w := w) es hn (hfr_fit.of_le (by omega)) hwts
  exact ⟨⟨hfr_fit, hwf.mem_fits⟩, rfl, hin⟩

/-! ## 1. Empty-edge (`m = 0`) and all-self-loop boundaries -/

example :
    let es : List (WeightedEdge 0 ℕ) := []
    let s₀ := mkRawInitState es
    let r := execWordRAM s₀ (initPreprocessProg ⟨0, 0, 0⟩)
    r.1.numVertices = 0 ∧ r.1.numEdges = 0 ∧ r.2.2 ≤ 9 := by
  intro es s₀ r
  dsimp only [r, s₀, es, execWordRAM]
  obtain ⟨hwf, hfr, hraw⟩ := mkRawInitState_spec (w := 16) es (by decide) (by decide)
    (fun _ h => by simp [es] at h)
  have hft := initPreprocessProg_spec (by decide) hwf hraw (by rw [hfr]; decide)
    (by rw [hfr]; decide)
  dsimp only [es, List.length_nil] at hft
  obtain ⟨_, hcost, _, hn, hm_le, hm, _, _, _, _, _, _, _, _, _, hinv⟩ :=
    framedTriple_iff_realization.mp hft
  have hsum := hinv.sum_le
  exact ⟨by omega, by omega, hcost⟩

example :
    let es : List (WeightedEdge 4 ℕ) := []
    let s₀ := mkRawInitState es
    let r := execWordRAM s₀ (initPreprocessProg ⟨4, 0, 0⟩)
    r.1.numVertices = 0 ∧ r.1.numEdges = 0 ∧ r.2.2 ≤ 45 := by
  intro es s₀ r
  dsimp only [r, s₀, es, execWordRAM]
  obtain ⟨hwf, hfr, hraw⟩ := mkRawInitState_spec (w := 16) es (by decide) (by decide)
    (fun _ h => by simp [es] at h)
  have hft := initPreprocessProg_spec (by decide) hwf hraw (by rw [hfr]; decide)
    (by rw [hfr]; decide)
  dsimp only [es, List.length_nil] at hft
  obtain ⟨_, hcost, _, hn, hm_le, hm, _⟩ := framedTriple_iff_realization.mp hft
  exact ⟨by omega, by omega, hcost⟩

private def selfLoops3Raw : List (WeightedEdge 3 ℕ) :=
  [⟨⟨0, by decide⟩, ⟨0, by decide⟩, 5⟩, ⟨⟨2, by decide⟩, ⟨2, by decide⟩, 1⟩]

example :
    let s₀ := mkRawInitState selfLoops3Raw
    let r := execWordRAM s₀ (initPreprocessProg ⟨3, selfLoops3Raw.length, 0⟩)
    r.1.numEdges = 0 ∧ r.1.numVertices = 0 ∧ r.2.2 ≤ 162 ∧
    (∀ e ∈ selfLoops3Raw, e.u = e.v) ∧
    IsMinSpanningForest selfLoops3Raw [] := by
  intro s₀ r
  dsimp only [r, s₀, execWordRAM]
  have hwts : ∀ e ∈ selfLoops3Raw, Fits 16 e.weight := by
    intro e he
    simp only [selfLoops3Raw, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> decide
  obtain ⟨hwf, hfr, hraw⟩ :=
    mkRawInitState_spec (w := 16) selfLoops3Raw (by decide) (by decide) hwts
  have hft := initPreprocessProg_spec (by decide) hwf hraw (by rw [hfr]; decide)
    (by rw [hfr]; decide)
  obtain ⟨_, hcost, _, hn_le, _, hm_le, _, _, _, _, es₀, hes₀_len, _, _, hall_self, hinv⟩ :=
    framedTriple_iff_realization.mp hft
  have hsum := hinv.sum_le
  have hall_loop : ∀ e ∈ selfLoops3Raw, e.u = e.v := fun e he => by
    simp only [selfLoops3Raw, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> rfl
  have hm0 : ((Memory.spec 0).clientResult (mkRawInitState selfLoops3Raw)
      (initPreprocessProg ⟨3, selfLoops3Raw.length, 0⟩)).numEdges = 0 :=
    hall_self.mpr hall_loop
  have hn0 : ((Memory.spec 0).clientResult (mkRawInitState selfLoops3Raw)
      (initPreprocessProg ⟨3, selfLoops3Raw.length, 0⟩)).numVertices = 0 := by omega
  have hes0 : es₀ = [] := List.length_eq_zero_iff.mp (hes₀_len.trans hm0)
  have hmsf0 : IsMinSpanningForest (es₀.map IndexedEdge.toWeighted)
      (([] : List (IndexedEdge ((Memory.spec 0).clientResult (mkRawInitState selfLoops3Raw)
        (initPreprocessProg ⟨3, selfLoops3Raw.length, 0⟩)).numVertices)).map
          IndexedEdge.toWeighted) := by
    rw [hes0]
    exact isMinSpanningForest_nil
  obtain ⟨remIds, hrem_val, hmsf_lift⟩ := hinv.2.2.2.2 [] List.nil_subperm hmsf0
  have hrem0 : remIds = [] := by
    cases remIds with
    | nil => rfl
    | cons _ _ => simp at hrem_val
  rw [hrem0, List.append_nil, List.map_nil] at hmsf_lift
  exact ⟨hm0, hn0, hcost, hall_loop, hmsf_lift⟩

example :
    let es : List (IndexedEdge 4) := []
    let s₀ := mkStageState es 0
    let r3 := execWordRAM s₀ (boruvkaThreeStageProg ⟨4, 0, 0, 0, 0⟩)
    r3.1.numVertices = 0 ∧ r3.1.numEdges = 0 ∧ r3.1.selOff = 0 ∧ r3.2.2 ≤ 534 := by
  intro es s₀ r3
  dsimp only [r3, s₀, es, execWordRAM]
  obtain ⟨hwf, hfr, hin⟩ := mkStageState_spec (w := 16) es (extra := 0) (by decide) (by decide)
    (fun _ h => by simp [es] at h)
  have hacc : ∀ j (hj : j < ([] : List (Fin ([] : List (WeightedEdge 4 ℕ)).length)).length),
      s₀.mem (0 + j) = ([] : List (Fin 0))[j].val := fun _ hj => by simp at hj
  have hinv : MSFLiftInv ([] : List (WeightedEdge 4 ℕ)) [] es :=
    ⟨List.nodup_nil, List.nodup_nil, fun _ h => by simp [es] at h,
      fun _ h => by simp at h, fun L hL _ => ⟨[], by simp [List.subperm_nil.mp hL],
        isMinSpanningForest_nil⟩⟩
  have ft3 := boruvkaThreeStageProg_spec (w := 16) (es := ([] : List (WeightedEdge 4 ℕ)))
    (accIds := []) (esCur := es) (selBase := 0) (by decide) hwf hin (by rw [hfr]; decide)
    hacc (by rw [hfr]; decide) hinv (by rw [hfr]; decide)
  dsimp only [es, s₀, List.length_nil] at ft3
  obtain ⟨_, hc3, _, h3v, h3off, h3sum, _⟩ := framedTriple_iff_realization.mp ft3
  exact ⟨by omega, by omega, by omega, hc3⟩

/-! ## 2. Multigraph preprocessing (`initPreprocessProg_spec`) -/

private def multiRaw5Edges : List (WeightedEdge 5 ℕ) :=
  [⟨⟨0, by decide⟩, ⟨0, by decide⟩, 1⟩,
   ⟨⟨0, by decide⟩, ⟨1, by decide⟩, 20⟩,
   ⟨⟨0, by decide⟩, ⟨1, by decide⟩, 5⟩,
   ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 7⟩,
   ⟨⟨0, by decide⟩, ⟨2, by decide⟩, 12⟩]

example :
    let s₀ := mkRawInitState multiRaw5Edges
    let r := execWordRAM s₀ (initPreprocessProg ⟨5, multiRaw5Edges.length, 0⟩)
    1 ≤ r.1.numEdges ∧ r.1.numEdges ≤ 5 ∧ r.1.numVertices ≤ 2 * r.1.numEdges ∧
    r.1.numVertices ≤ 5 ∧ r.2.2 ≤ 369 := by
  intro s₀ r
  dsimp only [r, s₀, execWordRAM]
  have hwts : ∀ e ∈ multiRaw5Edges, Fits 16 e.weight := by
    intro e he
    simp only [multiRaw5Edges, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨hwf, hfr, hraw⟩ := mkRawInitState_spec (w := 16) multiRaw5Edges (by decide) (by decide)
    hwts
  have hft := initPreprocessProg_spec (by decide) hwf hraw (by rw [hfr]; decide)
    (by rw [hfr]; decide)
  obtain ⟨_, hcost, _, hvn, hn5, hm5, _, _, _, _, _, _, _, _, hall_self, hinv⟩ :=
    framedTriple_iff_realization.mp hft
  have hsum := hinv.sum_le
  have hm_pos : 1 ≤ ((Memory.spec 0).clientResult (mkRawInitState multiRaw5Edges)
      (initPreprocessProg ⟨5, multiRaw5Edges.length, 0⟩)).numEdges := by
    by_contra h0
    have h0' : ((Memory.spec 0).clientResult (mkRawInitState multiRaw5Edges)
        (initPreprocessProg ⟨5, multiRaw5Edges.length, 0⟩)).numEdges = 0 := by omega
    have hloop := hall_self.mp h0' ⟨⟨0, by decide⟩, ⟨1, by decide⟩, 20⟩
      (by simp [multiRaw5Edges])
    simp at hloop
  have hlen : multiRaw5Edges.length = 5 := rfl
  exact ⟨hm_pos, by omega, hvn, hn5, hcost⟩

/-! ## 3. 3-stage Borůvka contraction and MSF lifting -/

private def stage9Raw : List (WeightedEdge 9 ℕ) :=
  [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 10⟩,
   ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 20⟩,
   ⟨⟨2, by decide⟩, ⟨3, by decide⟩, 30⟩,
   ⟨⟨3, by decide⟩, ⟨4, by decide⟩, 40⟩,
   ⟨⟨4, by decide⟩, ⟨5, by decide⟩, 50⟩,
   ⟨⟨5, by decide⟩, ⟨6, by decide⟩, 60⟩,
   ⟨⟨6, by decide⟩, ⟨7, by decide⟩, 70⟩,
   ⟨⟨7, by decide⟩, ⟨8, by decide⟩, 80⟩,
   ⟨⟨0, by decide⟩, ⟨2, by decide⟩, 99⟩,
   ⟨⟨4, by decide⟩, ⟨6, by decide⟩, 95⟩]

private theorem stage9Raw_wt_le : ∀ e ∈ stage9Raw, e.weight ≤ 100 := by
  intro e he
  simp only [stage9Raw, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private def stage9Indexed : List (IndexedEdge 9) :=
  stage9Raw.mapIdx fun i e => ⟨e.u, e.v, e.weight, i⟩

private theorem stage9_msf_lift_init : MSFLiftInv stage9Raw [] stage9Indexed := by
  have hid : stage9Indexed.map IndexedEdge.id = List.range stage9Raw.length := by
    apply List.ext_getElem <;> simp [stage9Indexed]
  have htw : stage9Indexed.map IndexedEdge.toWeighted = stage9Raw := by
    apply List.ext_getElem <;> simp [stage9Indexed, IndexedEdge.toWeighted]
  refine ⟨List.nodup_nil, by rw [hid]; exact List.nodup_range, ?_, fun _ h => by simp at h, ?_⟩
  · intro e he
    rw [stage9Indexed, List.mem_mapIdx] at he
    obtain ⟨i, hi, rfl⟩ := he
    exact hi
  · intro L hL hmsf
    have hL_lt : ∀ e ∈ L, e.id < stage9Raw.length := fun e he => by
      have hm := hL.subset he
      rw [stage9Indexed, List.mem_mapIdx] at hm
      obtain ⟨i, hi, rfl⟩ := hm
      exact hi
    let remIds : List (Fin stage9Raw.length) :=
      L.pmap (fun e he => ⟨e.id, hL_lt e he⟩) (fun _ he => he)
    refine ⟨remIds, by apply List.ext_getElem <;> simp [remIds], ?_⟩
    have hmap : (List.map (fun i => stage9Raw[i.val]) ([] ++ remIds)) =
        L.map IndexedEdge.toWeighted := by
      apply List.ext_getElem
      · simp [remIds]
      · intro i hi1 hi2
        have hi' : i < L.length := by simpa [remIds] using hi1
        have hm := hL.subset (List.getElem_mem hi')
        rw [stage9Indexed, List.mem_mapIdx] at hm
        obtain ⟨k, hk, heq⟩ := hm
        simp only [List.nil_append, List.getElem_map, List.getElem_pmap, remIds]
        simp only [← heq, IndexedEdge.toWeighted]
    rw [hmap, ← htw]
    exact hmsf

example :
    let selBase := 4 * stage9Indexed.length
    let s₀ := mkStageState stage9Indexed stage9Indexed.length
    let r3 := execWordRAM s₀ (boruvkaThreeStageProg ⟨9, stage9Indexed.length, 0, selBase, 0⟩)
    8 * r3.1.numVertices ≤ 9 ∧ r3.1.numVertices ≤ 1 ∧ r3.1.numEdges = 0 ∧
    r3.1.selOff ≤ 10 ∧ r3.2.2 ≤ 3414 ∧
    ∃ accIds : List (Fin stage9Raw.length),
      accIds.length = r3.1.selOff ∧
      (∀ j (hj : j < accIds.length), r3.2.1.mem (selBase + j) = accIds[j].val) ∧
      IsMinSpanningForest stage9Raw (accIds.map fun i => stage9Raw[i.val]) := by
  intro selBase s₀ r3
  dsimp only [r3, s₀, execWordRAM]
  have hwts : ∀ e ∈ stage9Indexed, Fits 16 e.weight ∧ Fits 16 e.id := fun e he => by
    rw [stage9Indexed, List.mem_mapIdx] at he
    obtain ⟨i, hi, rfl⟩ := he
    have hi10 : i < 10 := by simpa [stage9Raw] using hi
    exact ⟨(by decide : Fits 16 100).of_le (stage9Raw_wt_le _ (List.getElem_mem hi)),
      (by decide : Fits 16 10).of_le (by dsimp only; omega)⟩
  obtain ⟨hwf, hfr, hin⟩ :=
    mkStageState_spec (w := 16) stage9Indexed (extra := stage9Indexed.length) (by decide)
      (by decide) hwts
  have hlen : stage9Indexed.length = 10 := by decide
  have hacc : ∀ j (hj : j < ([] : List (Fin stage9Raw.length)).length),
      s₀.mem (selBase + j) = ([] : List (Fin stage9Raw.length))[j].val := fun _ hj => by
    simp at hj
  have ft3 := boruvkaThreeStageProg_spec (w := 16) (es := stage9Raw) (accIds := [])
    (esCur := stage9Indexed) (selBase := selBase) (by decide) hwf hin (by rw [hfr, hlen]; decide)
    hacc (by rw [hfr, hlen]; decide) stage9_msf_lift_init (by rw [hfr, hlen]; decide)
  dsimp only [s₀, List.length_nil] at ft3
  obtain ⟨_, hc3, _, h3v, _, h3sum, _, _, _, _, acc3, es3, hes3_len, _, h3simp, hacc3_len,
    hacc3_mem, hinv3⟩ := framedTriple_iff_realization.mp ft3
  have hsum3 := hinv3.sum_le
  have h3v1 : ((Memory.spec 0).clientResult (mkStageState stage9Indexed stage9Indexed.length)
      (boruvkaThreeStageProg ⟨9, stage9Indexed.length, 0, selBase, 0⟩)).numVertices ≤ 1 := by
    omega
  have hes3_nil : es3 = [] := eq_nil_of_isSimple_of_le_one h3v1 es3 h3simp
  have hm3 : ((Memory.spec 0).clientResult (mkStageState stage9Indexed stage9Indexed.length)
      (boruvkaThreeStageProg ⟨9, stage9Indexed.length, 0, selBase, 0⟩)).numEdges = 0 := by
    rw [← hes3_len, hes3_nil, List.length_nil]
  have hmsf3 : IsMinSpanningForest (es3.map IndexedEdge.toWeighted)
      (([] : List (IndexedEdge ((Memory.spec 0).clientResult
        (mkStageState stage9Indexed stage9Indexed.length)
        (boruvkaThreeStageProg
          ⟨9, stage9Indexed.length, 0, selBase, 0⟩)).numVertices)).map
          IndexedEdge.toWeighted) := by
    rw [hes3_nil]
    exact isMinSpanningForest_nil
  obtain ⟨remIds, hrem_val, hmsf_lift⟩ := hinv3.2.2.2.2 [] List.nil_subperm hmsf3
  have hrem0 : remIds = [] := by
    cases remIds with
    | nil => rfl
    | cons _ _ => simp at hrem_val
  rw [hrem0, List.append_nil] at hmsf_lift
  have hsel_le : ((Memory.spec 0).clientResult (mkStageState stage9Indexed stage9Indexed.length)
      (boruvkaThreeStageProg ⟨9, stage9Indexed.length, 0, selBase, 0⟩)).selOff ≤ 10 := by
    rw [← hacc3_len]
    have hraw10 : stage9Raw.length = 10 := rfl
    omega
  exact ⟨h3v, h3v1, hm3, hsel_le, hc3, acc3, hacc3_len, hacc3_mem, hmsf_lift⟩

/-! Non-empty initial `accIds` preservation across `boruvkaThreeStageProg_spec`. -/
example :
    let raw3 : List (WeightedEdge 3 ℕ) :=
      [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 2⟩,
       ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 4⟩]
    let curEs : List (IndexedEdge 2) :=
      [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 4, 1⟩]
    let accIds : List (Fin raw3.length) := [⟨0, by decide⟩]
    let s₀ : Memory.State :=
      ⟨fun a => if a = 4 * curEs.length then 0 else (mkInitState curEs).mem a,
       4 * curEs.length + accIds.length + curEs.length⟩
    let r := execWordRAM s₀ (boruvkaThreeStageProg ⟨2, curEs.length, 0, 4 * curEs.length, 1⟩)
    r.1.numVertices = 0 ∧ r.1.numEdges = 0 ∧ 1 ≤ r.1.selOff ∧ r.1.selOff ≤ 2 ∧
    r.2.1.mem (4 * curEs.length) = 0 := by
  intro raw3 curEs accIds s₀ r
  have hwts : ∀ e ∈ curEs, Fits 16 e.weight ∧ Fits 16 e.id := fun e he => by
    simp only [curEs, List.mem_singleton] at he
    subst he
    exact ⟨by decide, by decide⟩
  obtain ⟨hwf0, _, hin0⟩ := mkInitState_spec (w := 16) curEs (by decide) (by decide) hwts
  have hwf : Memory.WellFormed 16 s₀ := by
    refine ⟨by decide, fun a => ?_⟩
    by_cases ha : a = 4 * curEs.length
    · simp only [s₀, ha, ↓reduceIte]; decide
    · simp only [s₀, ha, ↓reduceIte]; exact hwf0.mem_fits a
  have hin : HoldsIndexedEdges 0 curEs s₀.mem := fun i hi => by
    obtain ⟨hu, hv, hw, hid⟩ := hin0 i hi
    refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only [s₀]
    · rw [ite_eq_right_iff.mpr (by omega)]; exact hu
    · rw [ite_eq_right_iff.mpr (by omega)]; exact hv
    · rw [ite_eq_right_iff.mpr (by omega)]; exact hw
    · rw [ite_eq_right_iff.mpr (by omega)]; exact hid
  have hacc : ∀ j (hj : j < accIds.length), s₀.mem (4 * curEs.length + j) = accIds[j].val := by
    intro j hj
    have hj0 : j = 0 := by simp [accIds] at hj; omega
    subst hj0
    simp [s₀, accIds]
  have hinv : MSFLiftInv raw3 accIds curEs := by
    refine ⟨by decide, by decide, fun e he => ?_, fun i hi e he => ?_, fun L hL hmsf => ?_⟩
    · simp only [curEs, List.mem_singleton] at he; subst he; decide
    · simp only [accIds, List.mem_singleton] at hi
      simp only [curEs, List.mem_singleton] at he
      subst hi; subst he; decide
    · have hlen : L.length ≤ 1 := hL.length_le
      rcases L with _ | ⟨e, L'⟩
      · have hrel := congrArg (fun p : DisjointSet.Partition 2 =>
            p.rel ⟨0, by decide⟩ ⟨1, by decide⟩) hmsf.1.2.2
        have hl : (edgePartition ([] : List (WeightedEdge 2 ℕ))).rel
            ⟨0, by decide⟩ ⟨1, by decide⟩ = false := by decide
        have hr : (edgePartition (curEs.map IndexedEdge.toWeighted)).rel
            ⟨0, by decide⟩ ⟨1, by decide⟩ = true := by decide
        simp only [List.map_nil] at hrel
        rw [hl, hr] at hrel
        cases hrel
      · simp only [List.length_cons] at hlen
        obtain rfl : L' = [] := List.length_eq_zero_iff.mp (by omega)
        obtain rfl : e = ⟨⟨0, by decide⟩, ⟨1, by decide⟩, 4, 1⟩ :=
          List.mem_singleton.mp (hL.subset List.mem_cons_self)
        refine ⟨[⟨1, by decide⟩], rfl, ?_⟩
        have hacyc : IsAcyclic raw3 := by
          refine isAcyclicFrom_cons.mpr ⟨by decide, isAcyclicFrom_cons.mpr
            ⟨by decide, isAcyclicFrom_nil _⟩⟩
        refine ⟨⟨List.Subperm.refl _, hacyc, rfl⟩, fun F' hF' => ?_⟩
        have hF'_len : F'.length ≤ 2 := hF'.1.length_le
        rcases F' with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
        · have hrel := congrArg (fun p : DisjointSet.Partition 3 =>
              p.rel ⟨0, by decide⟩ ⟨1, by decide⟩) hF'.2.2
          have hl : (edgePartition ([] : List (WeightedEdge 3 ℕ))).rel
              ⟨0, by decide⟩ ⟨1, by decide⟩ = false := by decide
          have hr : (edgePartition raw3).rel ⟨0, by decide⟩ ⟨1, by decide⟩ = true := by decide
          rw [hl, hr] at hrel
          cases hrel
        · have ha_mem := hF'.1.subset List.mem_cons_self
          simp only [raw3, List.mem_cons, List.not_mem_nil, or_false] at ha_mem
          rcases ha_mem with rfl | rfl
          · have hrel := congrArg (fun p : DisjointSet.Partition 3 =>
                p.rel ⟨1, by decide⟩ ⟨2, by decide⟩) hF'.2.2
            have hl : (edgePartition (n := 3) [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 2⟩]).rel
                ⟨1, by decide⟩ ⟨2, by decide⟩ = false := by decide
            have hr : (edgePartition raw3).rel ⟨1, by decide⟩ ⟨2, by decide⟩ = true := by decide
            rw [hl, hr] at hrel
            cases hrel
          · have hrel := congrArg (fun p : DisjointSet.Partition 3 =>
                p.rel ⟨0, by decide⟩ ⟨1, by decide⟩) hF'.2.2
            have hl : (edgePartition (n := 3) [⟨⟨1, by decide⟩, ⟨2, by decide⟩, 4⟩]).rel
                ⟨0, by decide⟩ ⟨1, by decide⟩ = false := by decide
            have hr : (edgePartition raw3).rel ⟨0, by decide⟩ ⟨1, by decide⟩ = true := by decide
            rw [hl, hr] at hrel
            cases hrel
        · have ha_mem := hF'.1.subset List.mem_cons_self
          have hb_mem := hF'.1.subset (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [raw3, List.mem_cons, List.not_mem_nil, or_false] at ha_mem hb_mem
          rcases ha_mem with rfl | rfl <;> rcases hb_mem with rfl | rfl
          · have hcnt := hF'.1.count_le (⟨⟨0, by decide⟩, ⟨1, by decide⟩, 2⟩ : WeightedEdge 3 ℕ)
            simp [raw3] at hcnt
          · decide
          · decide
          · have hcnt := hF'.1.count_le (⟨⟨1, by decide⟩, ⟨2, by decide⟩, 4⟩ : WeightedEdge 3 ℕ)
            simp [raw3] at hcnt
        · simp at hF'_len
  have ft := boruvkaThreeStageProg_spec (w := 16) (es := raw3) (accIds := accIds)
    (esCur := curEs) (selBase := 4 * curEs.length) (by decide) hwf hin (by decide) hacc
    (by decide) hinv (by decide)
  obtain ⟨_, _, hmod, h8v, hoff, hsum, _, _, _, _, acc', es', hes'_len, _, hsimp', hacc'_len, _,
    hinv'⟩ := framedTriple_iff_realization.mp ft
  have hkept := hmod.mem_eq_of_not_mem (a := 4 * curEs.length)
    (by dsimp only [s₀, curEs, accIds, List.length_cons, List.length_nil]; omega)
    (by simp only [Set.mem_Ico]
        dsimp only [curEs, accIds, List.length_cons, List.length_nil]; omega)
  have hv0 : ((Memory.spec 0).clientResult s₀
      (boruvkaThreeStageProg
        ⟨2, curEs.length, 0, 4 * curEs.length, accIds.length⟩)).numVertices = 0 := by omega
  have hes_nil : es' = [] := eq_nil_of_isSimple_of_le_one (by omega) es' hsimp'
  have hm0 : ((Memory.spec 0).clientResult s₀
      (boruvkaThreeStageProg
        ⟨2, curEs.length, 0, 4 * curEs.length, accIds.length⟩)).numEdges = 0 := by
    rw [← hes'_len, hes_nil, List.length_nil]
  have hsum_inv := hinv'.sum_le
  have hlen_a : accIds.length = 1 := rfl
  have hlen_r : raw3.length = 2 := rfl
  have hoff1 : 1 ≤ ((Memory.spec 0).clientResult s₀
      (boruvkaThreeStageProg
        ⟨2, curEs.length, 0, 4 * curEs.length, accIds.length⟩)).selOff := by omega
  have hoff2 : ((Memory.spec 0).clientResult s₀
      (boruvkaThreeStageProg
        ⟨2, curEs.length, 0, 4 * curEs.length, accIds.length⟩)).selOff ≤ 2 := by omega
  have hs0_kept : s₀.mem (4 * curEs.length) = 0 := by simp [s₀]
  exact ⟨hv0, hm0, hoff1, hoff2, hkept.trans hs0_kept⟩

/-! ## 4. Composite `realize` pipeline and lowered `Program .standard` execution -/

private def initAndBoruvkaThreeProg (a : InitPreprocessArgs) : Memory.Prog BoruvkaStageResult := do
  let g0 ← initPreprocessProg a
  let selBlk ← Memory.allocBlockDirty g0.numEdges
  boruvkaThreeStageProg ⟨g0.numVertices, g0.numEdges, g0.edgeBase, selBlk.base, 0⟩

private theorem allocDirty_cr (s : Memory.State) (k : ℕ) :
    (Memory.spec 0).clientResult s (Memory.allocBlockDirty k) = ⟨s.frontier, k⟩ := rfl

private theorem allocDirty_cs (s : Memory.State) (k : ℕ) :
    (Memory.spec 0).clientState s (Memory.allocBlockDirty k) = ⟨s.mem, s.frontier + k⟩ := rfl

private theorem initAndBoruvkaThreeProg_spec {w n inBase : ℕ}
    {es : List (WeightedEdge n ℕ)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hraw : HoldsEdges inBase es s.mem) (hin : inBase + 3 * es.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + (88 * es.length + 31 * n + 13))) :
    Memory.FramedTriple w s (initAndBoruvkaThreeProg ⟨n, es.length, inBase⟩)
      (297 * es.length + 117 * n + 112) ∅ fun res s' =>
        8 * res.numVertices ≤ n ∧
        res.edgeBase + 4 * res.numEdges ≤ s'.frontier ∧
        s'.frontier ≤ s.frontier + (88 * es.length + 31 * n + 13) ∧
        Memory.WellFormed w s' := by
  dsimp only [initAndBoruvkaThreeProg]
  have h1 := initPreprocessProg_spec h16 hwf hraw hin (hfit.of_le (by omega))
  refine (Memory.FramedTriple.bind_same (c₂ := 234 * es.length + 108 * n + 103)
    (h1.mono le_rfl fun g0 s₁ ⟨hg0_n2, hg0_n, hg0_m, _, hg0_fr, hs1_le, hwf1, es₀, hes₀_len,
      hholds0, _, _, hinv0⟩ => ?_)).mono (by omega) fun _ _ h => h
  have hfit_blk : Fits w (s₁.frontier + g0.numEdges) := hfit.of_le (by omega)
  have hholds0' : HoldsIndexedEdges g0.edgeBase es₀
      (⟨s₁.mem, s₁.frontier + g0.numEdges⟩ : Memory.State).mem := hholds0
  have hwf2 : Memory.WellFormed w ⟨s₁.mem, s₁.frontier + g0.numEdges⟩ :=
    ⟨hfit_blk, hwf1.mem_fits⟩
  have h3 := boruvkaThreeStageProg_spec (accIds := ([] : List (Fin es.length)))
    (selBase := s₁.frontier) h16 hwf2 hholds0' (by dsimp only; omega)
    (fun _ hj => by simp at hj) (by dsimp only; rw [hes₀_len, List.length_nil]; omega) hinv0
    (hfit.of_le (by dsimp only; rw [hes₀_len]; omega))
  rw [show (⟨g0.numVertices, es₀.length, g0.edgeBase, s₁.frontier,
      ([] : List (Fin es.length)).length⟩ : BoruvkaStageArgs) =
      ⟨g0.numVertices, g0.numEdges, g0.edgeBase, s₁.frontier, 0⟩ from by
        rw [hes₀_len]; rfl] at h3
  have hmem0 : ∀ x, x ∈ Set.Ico (s₁.frontier + ([] : List (Fin es.length)).length)
      (s₁.frontier + ([] : List (Fin es.length)).length + es₀.length) → s₁.frontier ≤ x :=
    fun _ hx => by simp only [Set.mem_Ico] at hx; omega
  refine ((Memory.FramedTriple.allocBlockDirty_bind (c := 234 * es.length + 108 * n + 102)
    hfit_blk ?_).frame_empty_of_ge_frontier hmem0).mono (by omega) fun _ _ h => h
  exact h3.mono (by rw [hes₀_len]; omega)
    fun res s₃ ⟨h3n, _, _, _, hed3_fr, hs3_le, hwf3, _⟩ => by
      dsimp only at hs3_le
      exact ⟨by omega, hed3_fr, by rw [hes₀_len] at hs3_le; omega, hwf3⟩

private theorem realizes_initAndBoruvkaThreeProg : Realizes .exact initAndBoruvkaThreeProg
    WordEncoding.encode WordEncoding.encode
    (fun w a s =>
      Fits w 16 ∧ a.inBase + 3 * a.numEdges ≤ s.frontier ∧
      Fits w (s.frontier + (88 * a.numEdges + 31 * a.numVertices + 13)) ∧
      ∀ j < a.numEdges,
        s.mem (a.inBase + 3 * j) < a.numVertices ∧
        s.mem (a.inBase + 3 * j + 1) < a.numVertices)
    (fun _ _ => 0) := by
  have hraw : Realizes .exact initAndBoruvkaThreeProg WordEncoding.encode WordEncoding.encode
      (fun w a s =>
        let g0 := (Memory.spec 0).clientResult s (initPreprocessProg a)
        let s₁ := (Memory.spec 0).clientState s (initPreprocessProg a)
        let selBlk := (Memory.spec 0).clientResult s₁ (Memory.allocBlockDirty g0.numEdges)
        let s₂ := (Memory.spec 0).clientState s₁ (Memory.allocBlockDirty g0.numEdges)
        initPreprocessProgSafe w a s ∧
        boruvkaThreeStageProgSafe w
          ⟨g0.numVertices, g0.numEdges, g0.edgeBase, selBlk.base, 0⟩ s₂)
      (fun _ _ => 0) := by
    unfold initAndBoruvkaThreeProg
    realize [realizes_initPreprocessProg, realizes_allocBlockDirty, realizes_boruvkaThreeStageProg]
    all_goals
      obtain ⟨hsafe1, hsafe3⟩ := h
      first
      | exact hsafe1 | trivial
  refine hraw.consequence (fun w a s _ hmem ⟨h16, hin_lt, hfit, hedges⟩ => ?_)
    (fun _ _ => le_rfl)
  rcases a with ⟨n, m, inBase⟩
  dsimp only at hin_lt hfit hedges ⊢
  have hsafe1 : initPreprocessProgSafe w ⟨n, m, inBase⟩ s := by
    refine ⟨h16, hin_lt, hfit.of_le (by dsimp only; omega), hedges⟩
  refine ⟨hsafe1, ?_⟩
  let rawEs : List (WeightedEdge n ℕ) := List.ofFn fun i : Fin m =>
    ⟨⟨s.mem (inBase + 3 * i.val), (hedges i.val i.isLt).1⟩,
      ⟨s.mem (inBase + 3 * i.val + 1), (hedges i.val i.isLt).2⟩,
      s.mem (inBase + 3 * i.val + 2)⟩
  have hlen : rawEs.length = m := List.length_ofFn
  have hraw_holds : HoldsEdges inBase rawEs s.mem := fun i hi => by simp [rawEs]
  have hp := framedTriple_iff_realization.mp
    (initPreprocessProg_spec h16 hmem hraw_holds (by rw [hlen]; exact hin_lt)
      (by rw [hlen]; exact hfit.of_le (by omega)))
  rw [show (⟨n, rawEs.length, inBase⟩ : InitPreprocessArgs) = ⟨n, m, inBase⟩ from by
    rw [hlen]] at hp
  obtain ⟨_, _, _, _, hn_le, hm_le, _, hed_fr, hs1_le, hwf1, es₀, hes₀_len, hholds0, _⟩ := hp
  rw [hlen] at hm_le hs1_le
  rw [allocDirty_cr, allocDirty_cs]
  refine ⟨h16, by dsimp only; omega, by dsimp only; omega, hfit.of_le (by dsimp only; omega),
    fun j hj => ?_⟩
  have hj' : j < es₀.length := hes₀_len.symm ▸ hj
  obtain ⟨hu, hv, _, _⟩ := hholds0 j hj'
  exact ⟨hu ▸ (es₀[j]'hj').u.isLt, hv ▸ (es₀[j]'hj').v.isLt⟩

example :
    let words : List ℕ :=
      [5, 5, 4, 0, 1, 2, 1, 2, 3, 2, 3, 4, 3, 4, 5, 0, 4, 20]
    let a : InitPreprocessArgs := ⟨5, 5, 4⟩
    ∃ r C pc : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
      ∃ frontier : Fin r, ∃ y n,
        Runs 16 prog (State.init words) ⟨pc, y⟩ n ∧
        step 16 prog ⟨pc, y⟩ =
          .halt ((Memory.spec 16).clientResult (Memory.State.init words)
            (initAndBoruvkaThreeProg a)).numVertices ∧
        (memoryState frontier y).frontier =
          ((Memory.spec 16).clientState (Memory.State.init words)
            (initAndBoruvkaThreeProg a)).frontier ∧
        n + 1 ≤ C * (memoryCost (initAndBoruvkaThreeProg a) (Memory.State.init words) + 1) + 1 := by
  intro words a
  obtain ⟨r, C, pc, prog, hnw, frontier, _, hrun⟩ :=
    realizes_initAndBoruvkaThreeProg.exists_standard_basis_init_program_state_from_words (0 : Fin 4)
  have hwf : Memory.WellFormed 16 (Memory.State.init words) :=
    Memory.wellFormed_init (by decide) (by decide)
  have hlayout : ∀ j : Fin 3, words.getD j.val 0 = WordEncoding.encode a j := by
    intro j; fin_cases j <;> rfl
  have hedges : ∀ j < a.numEdges,
      (Memory.State.init words).mem (a.inBase + 3 * j) < a.numVertices ∧
      (Memory.State.init words).mem (a.inBase + 3 * j + 1) < a.numVertices := by
    intro j hj
    dsimp only [a] at hj ⊢
    rcases j with _ | _ | _ | _ | _ | j
    · decide
    · decide
    · decide
    · decide
    · decide
    · omega
  have hpre : Fits 16 16 ∧ a.inBase + 3 * a.numEdges ≤ (Memory.State.init words).frontier ∧
      Fits 16 ((Memory.State.init words).frontier + (88 * a.numEdges + 31 * a.numVertices + 13)) ∧
      ∀ j < a.numEdges,
        (Memory.State.init words).mem (a.inBase + 3 * j) < a.numVertices ∧
        (Memory.State.init words).mem (a.inBase + 3 * j + 1) < a.numVertices :=
    ⟨by decide, by decide, by decide, hedges⟩
  let rawEs : List (WeightedEdge 5 ℕ) :=
    [⟨0, 1, 2⟩, ⟨1, 2, 3⟩, ⟨2, 3, 4⟩, ⟨3, 4, 5⟩, ⟨0, 4, 20⟩]
  have hraw : HoldsEdges 4 rawEs (Memory.State.init words).mem := by
    intro i hi
    rcases i with _ | _ | _ | _ | _ | i
    · simp only [words, rawEs, List.getElem_cons_zero]; decide
    · simp only [words, rawEs, List.getElem_cons_zero, List.getElem_cons_succ]; decide
    · simp only [words, rawEs, List.getElem_cons_zero, List.getElem_cons_succ]; decide
    · simp only [words, rawEs, List.getElem_cons_zero, List.getElem_cons_succ]; decide
    · simp only [words, rawEs, List.getElem_cons_zero, List.getElem_cons_succ]; decide
    · dsimp only [rawEs] at hi; simp only [List.length_cons, List.length_nil] at hi; omega
  have hv := (framedTriple_iff_realization.mp (initAndBoruvkaThreeProg_spec (by decide) hwf hraw
    (by decide) (by decide))).1
  obtain ⟨y, n, hruns, hhalt, hmem_eq, _, hsteps⟩ :=
    hrun 16 a words hlayout (by decide) (by decide) (by decide) hpre hv
  refine ⟨r, C, pc, stripRand prog, not_readsWidth_stripRand hnw, isRandFree_stripRand prog,
    frontier, y, n, runs_stripRand hruns, step_stripRand_of_halt hhalt, ?_, ?_⟩
  · rw [hmem_eq]
  · simpa only [Nat.add_zero] using hsteps

end CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSFBoruvkaStages
